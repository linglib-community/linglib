module

public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Dargwa.Tanti.Locatives

/-!
# Tanti Dargwa voice

This file defines the valency alternations of Tanti Dargwa as Sumbatova describes them. The
causative *-aq* is the only valency-changing morphology: the causee of an intransitive base is
the absolutive P of the derived clause, that of a transitive base an oblique in the
inter-elative, a locative form without the direction marker every spatial elative carries. The
antipassive is uncoded and confined to imperfective forms, and some transitive forms are
P-labile, the preterite *če-b-asː-un* meaning 'he glued it' or 'it stuck' where the future
tells the two apart by its thematic suffix.

## Main definitions

* `Dargwa.Tanti.antipassive`, `Dargwa.Tanti.anticausative`, `Dargwa.Tanti.causativeOfIntransitive`,
  `Dargwa.Tanti.causativeOfTransitive`, `Dargwa.Tanti.alternations`: the valency alternations
* `Dargwa.Tanti.causeeForm`: the inter-elative of the causee of a transitive base

## Main results

* `Dargwa.Tanti.isCoded_iff`: the two causatives are the alternations coded on the verb
* `Dargwa.Tanti.causativeOfIntransitive_fateOfRole_S`, `Dargwa.Tanti.causativeOfTransitive_valency`:
  the causee of an intransitive base stays a core term; that of a transitive base is demoted as the
  causer is introduced, so the valency is unchanged
* `Dargwa.Tanti.not_isSpatial_causeeForm`, `Dargwa.Tanti.causeeForm_morphs`: the causee form is the
  directionless elative no spatial form is, *-cːe-r* after the oblique stem
* `Dargwa.Tanti.labile_future_thematic`: the future forms of a P-labile verb differ in their
  thematic suffix

## Implementation notes

* The demoted causee and the antipassive patient are adpositional positions of the derived
  frame, the frame vocabulary's oblique; the case each takes is stated with the voice.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
* [D. Creissels, *Transitivity, Valency, and Voice* (2024)][creissels-2024]
-/

@[expose] public section

namespace Dargwa.Tanti

open ArgumentFrame.Slot Morphology

/-- The antipassive is uncoded and confined to imperfective forms. The A is absolutive and the
P is demoted to an ergative that controls no agreement; affective verbs have none. -/
def antipassive : Voice := .antipassive

/-- P-lability is the uncoded anticausative of a transitive form, mostly of verbs of
situations that occur with or without an agent, whose patient is then the S. -/
def anticausative : Voice := .anticausative

/-- The causative *-aq* of an intransitive verb. The causer is the ergative A and the causee,
the initial S, the absolutive P. -/
def causativeOfIntransitive : Voice := Voice.causative.marked [.suff "aq"]

/-- The causative *-aq* of a transitive verb. The causer is the ergative A and the causee, the
initial A, an oblique in the inter-elative. -/
def causativeOfTransitive : Voice :=
  (Voice.of .np ⟨some .nominal, [.nominal, .adpositional]⟩
    [some (complement 1), some (complement 0), some external]).marked [.suff "aq"]

/-- The inter-elative of the causee of a transitive base, a locative form without a direction
marker. -/
def causeeForm : LocativeForm := ⟨.inter, .elative, none⟩

/-- The valency alternations of Tanti. -/
def alternations : Finset Voice :=
  {antipassive, anticausative, causativeOfIntransitive, causativeOfTransitive}

/-- The causative is the only alternation coded on the verb. -/
theorem isCoded_iff {v : Voice} (hv : v ∈ alternations) :
    v.IsCoded ↔ v = causativeOfIntransitive ∨ v = causativeOfTransitive := by
  simp only [alternations, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

/-- The causee of an intransitive base stays a core term, the P of the derived construction. -/
theorem causativeOfIntransitive_fateOfRole_S :
    causativeOfIntransitive.fateOfRole .S = .maintained := by decide

/-- The causative of a transitive base introduces the causer as it demotes the causee, so the
derived construction has the valency of the initial one. -/
theorem causativeOfTransitive_valency :
    causativeOfTransitive.Nucleativizes ∧
      causativeOfTransitive.fateOfRole .A = .denucleativized ∧
      causativeOfTransitive.derived.valency = causativeOfTransitive.initial.valency := by
  decide

/-- The causee form is an elative without a direction marker, which no spatial elative is. -/
theorem not_isSpatial_causeeForm : ¬ causeeForm.IsSpatial :=
  LocativeForm.not_isSpatial_elative_none _

/-- The causee *durʜaˁ-li-cːe-r* 'the boy' takes *-cːe-r* after the oblique stem. -/
theorem causeeForm_morphs (g : Gender.Marker) :
    causeeForm.morphs g = [.suff "cːe", .suff "r"] := rfl

/-- The future forms of a P-labile verb with third-person arguments are told apart by the
thematic suffix, *-u* for *če-b-alsː-u* '(he) will glue it' and *-ar* for *če-b-alsː-ar* 'it
will stick'. -/
theorem labile_future_thematic :
    thematic ⟨.third, .third⟩ = .suff "u" ∧ .suff "ar" ∈ intransitiveThematic .third := by
  decide

end Dargwa.Tanti
