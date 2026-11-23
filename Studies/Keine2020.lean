module

public import Linglib.Syntax.Minimalist.Probe.Horizon
public import Linglib.Data.Examples.Keine2020
public import Linglib.Data.Examples.Readers
public import Studies.Keine2019

/-!
# Keine (2020): Probes and Their Horizons

A probe searches its c-command domain up to the first node that bears its horizon category, and
a clause bears every category its extended projection projects, so an embedded clause is
transparent to a probe exactly when it does not project the probe's horizon. [keine-2020] sets
the horizons of the Hindi probes as follows: A-movement and φ-agreement, on T⁰, have horizon T;
wh-licensing, on C⁰, has horizon C; Ā-movement, on C⁰, has horizon Nmlz.

A Hindi sentence shows dependencies across an embedded clause: movement out of it, with or
without binding from the landing site, long-distance or default agreement on the matrix verb,
matrix scope of a wh-phrase inside it. The surface type of the clause leaves its size open, an
infinitive being a vP or a TP. We say a sentence is derivable when some size its clause may have
licenses every dependency it shows, where default agreement requires a clause opaque to
φ-agreement, agreement being obligatory where it is possible. Derivability matches the judgment
of each example sentence. Since the two probes on T⁰ share a horizon, no sentence in which a
phrase binds from a landing site outside a clause shows default agreement into that clause,
whatever else it shows.

The nominalized clause and the finite clause are incomparable in size, and wh-licensing and
Ā-movement each enter the one and not the other. The English and German probes are stated on
the clause sizes of one extended projection, where the clauses transparent to a probe are those
inside the complement of its horizon. The A-movement probes of Hindi, English and Lubukusu, all
on T⁰, form a scale of successively higher horizons.

## Implementation notes

The probes that [keine-2019] already has are that study's definitions. The Ā-movement probe
differs: the article gives it no horizon, and the book gives it the horizon Nmlz, which the
article's three clause sizes do not project.

A row records the dependencies a sentence shows, not the probes that underlie them. Movement
that binds a pronoun or a reciprocal from its landing site is A-movement; movement that does not
is A-movement or Ā-movement.

## TODO

* The English and German examples behind the two languages' probes are not rows.
* The interaction of horizons with CP and vP phases, which restricts agreement in Tsez to the
  edge of the clause, is not formalized.

## References

* [keine-2020]
* [keine-2019]
* [bhatt-2005]
* [bobaljik-wurmbrand-2005]
* [polinsky-potsdam-2001]
-/

@[expose] public section

namespace Keine2020

open Minimalist

/-! ### Clause sizes -/

/-- The Hindi nominalized clause `[V, v, T, Nmlz]`, a gerund: Nmlz⁰ selects a TP. -/
def nmlzP : Spine := ⟨[.V, .v, .T, .Nmlz]⟩

/-- The German verb-second clause `[V, v, T, C, Force]`, a ForceP above the CP. -/
def forceP : Spine := ⟨[.V, .v, .T, .C, .Force]⟩

theorem nmlzP_isExtendedProjection : nmlzP.IsExtendedProjection := by decide +kernel

theorem forceP_isExtendedProjection : forceP.IsExtendedProjection := by decide +kernel

-- (168)
theorem nmlzP_cP_incomparable : ¬ nmlzP ≤ Spine.cP ∧ ¬ Spine.cP ≤ nmlzP := by decide

/-! ### The Hindi probes -/

/-- (219d): the Ā-movement probe, on C⁰ with horizon Nmlz. -/
def ābarProbe : HorizonSetting := ⟨.C, some .Nmlz⟩

theorem ābarProbe_transparentTo_iff {s : Spine} (hs : Cat.Nmlz ∉ s) :
    ābarProbe.TransparentTo s ↔ Keine2019.ābarProbe.TransparentTo s := by
  simp [ābarProbe, Keine2019.ābarProbe, hs]

/-- Wh-licensing enters the nominalized clause and not the finite one, and Ā-movement the finite
clause and not the nominalized one. -/
theorem whLicensing_ābarProbe_cross :
    (Keine2019.whLicensing.TransparentTo nmlzP ∧ ¬ Keine2019.whLicensing.TransparentTo .cP) ∧
      ābarProbe.TransparentTo .cP ∧ ¬ ābarProbe.TransparentTo nmlzP := by
  decide

/-! ### Dependencies across a clause -/

/-- The sizes a clause of each surface type may have: a finite clause is a CP and a gerund an
NmlzP; an infinitive is a vP or a TP, and a TP when it hosts a temporal adverb or a negation. -/
def Examples.Clause.sizes : Examples.Clause → List Spine
  | .finite => [.cP]
  | .infinitive => [.vP, .tP]
  | .modifiedInfinitive => [.tP]
  | .gerund => [nmlzP]

/-- The condition a dependency puts on a clause of size `s` that it crosses. Binding from the
landing site requires A-movement and movement without it A-movement or Ā-movement; default
agreement requires that φ-agreement be impossible. -/
def Examples.Dependency.LicensedAt (s : Spine) : Examples.Dependency → Prop
  | .binding => Keine2019.aProbe.TransparentTo s
  | .movement => Keine2019.aProbe.TransparentTo s ∨ ābarProbe.TransparentTo s
  | .lda => Keine2019.phiProbe.TransparentTo s
  | .defaultAgreement => ¬ Keine2019.phiProbe.TransparentTo s
  | .whScope => Keine2019.whLicensing.TransparentTo s

instance (s : Spine) : DecidablePred (Examples.Dependency.LicensedAt s) := fun d ↦ by
  cases d <;> unfold Examples.Dependency.LicensedAt <;> infer_instance

/-- A sentence that shows the dependencies `ds` across a clause of type `c` is derivable when
some size the clause may have licenses each of them. -/
def Derivable (c : Examples.Clause) (ds : List Examples.Dependency) : Prop :=
  ∃ s ∈ c.sizes, ∀ d ∈ ds, d.LicensedAt s

instance (c : Examples.Clause) (ds : List Examples.Dependency) : Decidable (Derivable c ds) :=
  inferInstanceAs (Decidable (∃ s ∈ _, _))

/-- The horizons of the Hindi probes derive the judgment of each of the twenty example
sentences. -/
theorem judgments_derived :
    Datum.Checks (fun e ↦ (Examples.clause e).map (·, Examples.dependencies e))
      (fun ⟨c, ds⟩ ↦ .ofProp (Derivable c ds)) Examples.all 20 := by
  decide

/-- The A-Movement–Agreement Generalization: a sentence in which a phrase binds from a landing
site outside a clause does not show default agreement into that clause. -/
theorem not_derivable_of_binding_of_defaultAgreement {c : Examples.Clause}
    {ds : List Examples.Dependency} (hb : .binding ∈ ds) (hd : .defaultAgreement ∈ ds) :
    ¬ Derivable c ds :=
  fun ⟨_, _, h⟩ ↦ h _ hd (h _ hb)

-- (96b)
theorem derivable_movement_defaultAgreement :
    Derivable .infinitive [.movement, .defaultAgreement] := by
  decide

/-! ### English and German -/

/-- (241b): the English wh-probe, on C⁰ without horizon. -/
def englishWh : HorizonSetting := ⟨.C, none⟩

-- (241)
theorem english_profiles {t : Spine} (ht : t.heads <+: Spine.cP.heads) :
    (Keine2019.englishAProbe.TransparentTo t ↔ t ≤ .tP) ∧
      (Keine2019.extrapositionProbe.TransparentTo t ↔ t ≤ .vP) ∧ englishWh.TransparentTo t :=
  ⟨(HorizonSetting.transparentTo_mk_some_iff_le_below ht).trans (by rw [Spine.cP_below_C]),
    (HorizonSetting.transparentTo_mk_some_iff_le_below ht).trans (by rw [Spine.cP_below_T]),
    HorizonSetting.transparentTo_mk_none⟩

/-- (367a): German scrambling, on T⁰ with horizon T. -/
def germanScr : HorizonSetting := .default .T

/-- (367b): German relativization, on C⁰ with horizon C. -/
def germanRel : HorizonSetting := .default .C

/-- (367c): German wh-movement into a verb-final clause, on C⁰ with horizon Force. -/
def germanWh : HorizonSetting := ⟨.C, some .Force⟩

/-- (367d): German topicalization, on Force⁰ without horizon. -/
def germanTop : HorizonSetting := ⟨.Force, none⟩

/-- The four German movements leave successively larger clauses: scrambling the coherent
infinitive, relativization also the noncoherent one, wh-movement also the verb-final finite
clause, and topicalization every clause. -/
theorem german_profiles {t : Spine} (ht : t.heads <+: forceP.heads) :
    (germanScr.TransparentTo t ↔ t ≤ .vP) ∧ (germanRel.TransparentTo t ↔ t ≤ .tP) ∧
      (germanWh.TransparentTo t ↔ t ≤ .cP) ∧ germanTop.TransparentTo t :=
  ⟨(HorizonSetting.transparentTo_mk_some_iff_le_below ht).trans
      (by rw [show forceP.below .T = .vP by decide]),
    (HorizonSetting.transparentTo_mk_some_iff_le_below ht).trans
      (by rw [show forceP.below .C = .tP by decide]),
    (HorizonSetting.transparentTo_mk_some_iff_le_below ht).trans
      (by rw [show forceP.below .Force = .cP by decide]),
    HorizonSetting.transparentTo_mk_none⟩

/-! ### Movement and agreement in Itelmen and Tsez -/

/-- (269a): Itelmen φ-agreement, with horizon T. -/
def itelmenPhi (head : Cat) : HorizonSetting := ⟨head, some .T⟩

/-- (269b): Itelmen movement, without horizon. -/
def itelmenMove (head : Cat) : HorizonSetting := ⟨head, none⟩

/-- (271a): Tsez φ-agreement, with horizon Force. -/
def tsezPhi (head : Cat) : HorizonSetting := ⟨head, some .Force⟩

/-- (271b): Tsez movement, with horizon Top. -/
def tsezMove (head : Cat) : HorizonSetting := ⟨head, some .Top⟩

/-- The Tsez clause `[V, v, T, Top]`. -/
def tsezTopP : Spine := ⟨[.V, .v, .T, .Top]⟩

/-- The Tsez clause `[V, v, T, Top, Force]`, whose ForceP requires a TopP below it. -/
def tsezForceP : Spine := ⟨[.V, .v, .T, .Top, .Force]⟩

-- (269), (271)
theorem mismatches (head : Cat) :
    ((itelmenMove head).TransparentTo Spine.tP ∧
        ¬ (itelmenPhi head).TransparentTo Spine.tP) ∧
      ((tsezPhi head).TransparentTo tsezTopP ∧
        ¬ (tsezMove head).TransparentTo tsezTopP) ∧
      ¬ (tsezPhi head).TransparentTo tsezForceP ∧
        ¬ (tsezMove head).TransparentTo tsezForceP := by
  simp [itelmenMove, itelmenPhi, tsezPhi, tsezMove, tsezTopP, tsezForceP, Spine.tP]

/-! ### Height and locality -/

-- (274), (278)
theorem vacuous_on_C {h : Cat} (hh : h ∈ Spine.tP) :
    (⟨.C, some h⟩ : HorizonSetting).IsVacuousIn .cP := by
  simpa using hh

-- (219), (241), (367), (279)
theorem attested_nonvacuous :
    ∀ p ∈ [Keine2019.aProbe, Keine2019.phiProbe, Keine2019.whLicensing, ābarProbe,
      Keine2019.englishAProbe, englishWh, Keine2019.extrapositionProbe,
      germanScr, germanRel, germanWh, germanTop], ¬ p.IsVacuousIn forceP := by
  decide

/-- (300): the Lubukusu A-movement probe, on T⁰ without horizon. -/
def lubukusuAProbe : HorizonSetting := ⟨.T, none⟩

/-- The A-movement probes of Hindi, English and Lubukusu form a scale: a clause that Hindi
A-movement leaves, English A-movement leaves, and a clause that English A-movement leaves,
Lubukusu A-movement leaves. -/
theorem a_movement_scale {t : Spine} (ht : t.heads <+: Spine.cP.heads) :
    (Keine2019.aProbe.TransparentTo t → Keine2019.englishAProbe.TransparentTo t) ∧
      (Keine2019.englishAProbe.TransparentTo t → lubukusuAProbe.TransparentTo t) :=
  ⟨.of_default (p := Keine2019.englishAProbe) (s := .cP) (by decide) ht,
    fun _ ↦ HorizonSetting.transparentTo_mk_none⟩

-- Section 6.2
theorem improper_movement {h : Cat} (hh : h ∈ Spine.cP) :
    ¬ (⟨.T, some h⟩ : HorizonSetting).TransparentTo Spine.cP := by
  simpa using hh

end Keine2020
