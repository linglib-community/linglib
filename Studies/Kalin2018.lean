module

public import Linglib.Data.Examples.Kalin2018
public import Linglib.Syntax.Minimalist.Case.Dependent
public import Linglib.Core.Data.List.Forall2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.Minimal

/-!
# Kalin (2018): Licensing and Differential Object Marking

This file formalizes [kalin-2018], which derives differential object marking from nominal
licensing rather than from object visibility, raising or differentiation. Two parameters
interact: which nominals require licensing, in Senaya only the specific ones, and where the
licensers are, every clause carrying an obligatory licenser that licenses the closest nominal
whatever its needs, and secondary licensers that merge only when the derivation would otherwise
crash, the Licensing Economy Principle, (36). In Senaya the marking is verbal agreement: in the
imperfective, Asp is the obligatory licenser and agrees with the subject as an S-suffix, and T is
a secondary licenser that agrees with a specific object as an L-suffix, (43) and (47); in the
perfective, Asp is no licenser and T is obligatory, so T agrees with the subject and a specific
object cannot be licensed at all, (49) and (50), the ban of (12). The licensing derivation
reproduces the agreement data (8) to (12) and (38) whatever the specificity of the subject
(`rows_agree`), and the toy nominative-accusative language of §3.1 shows differential marking by
a secondary v (`toy_animate_object`, `toy_inanimate_object`). The perfective ban is the paper's
argument against a theory without licensing: the dependent-case rules of [marantz-1991] value the
perfective object accusative, but a specific object there crashes
(`dependentCase_values_banned_object`).

The theory is formalized first. Every nominal bears a Case feature, unvalued unless a lexical
head has valued it, so every nominal is visible to a licenser; only some bear *uninterpretable*
Case ([pesetsky-torrego-2007]), and those alone crash the derivation when it goes unvalued. A
licenser is a head with a φ-probe that Agrees with the highest nominal in the phase domain it
probes whose Case is unvalued, the Agree of `Minimalist.agreeValue`, and a secondary licenser
merges only as a last resort ([rezac-2011]). The derivation never sees which nominals need
licensing, since it runs on positions alone, and needs are read only by convergence. Licensing
is monotone in the licensers (`license_mono`), so the Licensing Economy Principle stated for each
secondary licenser coincides with the preference for a derivation with fewer licensers
(`economical_iff`). Licensing is the Agree modality of case assignment of
[baker-vinokurova-2010]: case assigners with no dependent or elsewhere case assign exactly what
the licensing derivation does (`assign_eq_map_license`).

## Implementation notes

* The agreement suffix is read off the licensing head, the S-suffix from Asp and the L-suffix
  from T, the analysis of [kalin-van-urk-2015] that the paper adopts in §4.1.
* In Senaya v is not a phase head (§4.1), so both arguments are in the domain T and Asp probe;
  in the toy language the object is in the domain of v, which the subject is not.
* Nominals are listed from the highest down; the licensers probing one phase domain are listed in
  merge order, the lowest first, and the domains spell out in the order given.
* Only structural licensing under c-command is modelled: an inherent licenser that values only
  its specifier is not.
* Word order and the position of agreement within the verbal complex are not modelled.

## References

* [kalin-2018]
* [kalin-van-urk-2015]
* [pesetsky-torrego-2007]
* [rezac-2011]
* [baker-vinokurova-2010]
* [marantz-1991]
-/

@[expose] public section

namespace Kalin2018

open Minimalist
open Case (Valuation)

section Licensing

open List

/-! ### Licensers and nominals -/

/-- Whether a licenser merges in every derivation or only as a last resort. -/
inductive LicenserKind where
  | obligatory
  | secondary
  deriving DecidableEq, Repr

/-- A licenser: a head with a φ-probe, the phase whose domain it probes, and whether it merges in
every derivation. -/
structure Licenser where
  head : Cat
  domain : Cat := .C
  kind : LicenserKind
  deriving DecidableEq, Repr

/-- A nominal together with whether it bears uninterpretable Case and so needs licensing. -/
structure LicensedNP extends PhasedNP where
  needsLicensing : Bool
  deriving DecidableEq, Repr

/-- What valued a nominal's Case: a lexical head, with the case it assigned, or a licenser. -/
inductive CaseValue where
  | lexical (c : _root_.Case)
  | licenser (l : Licenser)
  deriving DecidableEq, Repr

/-! ### The derivation -/

/-- The Case of each nominal before any licenser probes: valued only by a lexical head. -/
def initial (nps : List PhasedNP) : Valuation PhasedNP CaseValue :=
  Valuation.initial (·.lexicalCase.map .lexical) nps

/-- The Agree of licenser `l`. -/
def Licenser.agree (l : Licenser) : Valuation PhasedNP CaseValue → Valuation PhasedNP CaseValue :=
  agreeValue (·.visible l.domain) (.licenser l)

/-- The licensers probing the domain of `c` merge, the lowest first. -/
def cycle (ls : List Licenser) (c : Cat) (st : Valuation PhasedNP CaseValue) :
    Valuation PhasedNP CaseValue :=
  (ls.filter (·.domain == c)).foldl (fun st l ↦ l.agree st) st

/-- The derivation: the phase domains `ds` spell out in order, each with its licensers. -/
def license (ds : List Cat) (ls : List Licenser) (nps : List PhasedNP) :
    Valuation PhasedNP CaseValue :=
  ds.foldl (fun st c ↦ cycle ls c st) (initial nps)

/-- A derivation converges iff every nominal that needs licensing has its Case valued. -/
def Converges (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP) : Prop :=
  Forall₂ (fun np p ↦ np.needsLicensing → p.2.isSome) nps (license ds ls (nps.map (·.toPhasedNP)))

instance (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP) :
    Decidable (Converges ds ls nps) :=
  inferInstanceAs (Decidable (Forall₂ _ _ _))

/-- A nominal is DOM-marked iff a secondary licenser valued its Case. -/
def IsDOMMarked : Option CaseValue → Prop
  | some (.licenser l) => l.kind = .secondary
  | _ => False

instance : DecidablePred IsDOMMarked
  | some (.licenser l) => inferInstanceAs (Decidable (l.kind = .secondary))
  | some (.lexical _) | none => inferInstanceAs (Decidable False)

section Derivation

variable {l : Licenser} {ds : List Cat} {ls ls' : List Licenser} {nps : List LicensedNP}

theorem agree_cons_none {np : PhasedNP} (hnp : np.visible l.domain)
    (s : Valuation PhasedNP CaseValue) :
    l.agree ((np, none) :: s) = (np, some (.licenser l)) :: s := by
  simp [Licenser.agree, hnp]

theorem agree_cons_some (np : PhasedNP) (v : CaseValue) (s : Valuation PhasedNP CaseValue) :
    l.agree ((np, some v) :: s) = (np, some v) :: l.agree s := by
  simp [Licenser.agree]

theorem extends_license (ds : List Cat) (ls : List Licenser) (nps : List PhasedNP) :
    (initial nps).Extends (fun v ↦ ∀ l, v = .licenser l → l ∈ ls) (license ds ls nps) :=
  Valuation.Extends.foldl _ (fun c _ st ↦ Valuation.Extends.foldl _
    (fun l hl st ↦ extends_agreeValue (fun _ h ↦ by cases h; exact mem_of_mem_filter hl) st) st) _

@[simp]
theorem length_license (ds : List Cat) (ls : List Licenser) (nps : List PhasedNP) :
    (license ds ls nps).length = nps.length := by
  simp [← (extends_license ds ls nps).length_eq, initial]

theorem mem_of_mem_license {nps : List PhasedNP} {np : PhasedNP}
    (h : (np, some (.licenser l)) ∈ license ds ls nps) : l ∈ ls := by
  rcases (extends_license ds ls nps).of_mem h with h | h
  · simp [initial, Valuation.initial] at h
  · exact h l rfl

/-! ### Monotonicity -/

private theorem forall₂_trans {α β γ : Type*} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (hRST : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ l₂ l₃}, Forall₂ R l₁ l₂ → Forall₂ S l₂ l₃ → Forall₂ T l₁ l₃
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ h₂, .cons h₃ h₄ =>
    .cons (hRST _ _ _ h₁ h₃) (forall₂_trans hRST h₂ h₄)

private theorem valuedLE_foldl_agree :
    ∀ {L L' : List Licenser}, L <+ L' → ∀ {s t : Valuation PhasedNP CaseValue}, s.ValuedLE t →
      (L.foldl (fun st l ↦ l.agree st) s).ValuedLE (L'.foldl (fun st l ↦ l.agree st) t)
  | _, _, .slnil, _, _, h => h
  | _, _, .cons l hL, _, _, h =>
    valuedLE_foldl_agree hL (h.trans (valuedLE_agreeValue _))
  | _, _, .cons_cons l hL, _, _, h => valuedLE_foldl_agree hL h.agreeValue

theorem license_mono (h : ls <+ ls') (ds : List Cat) (nps : List PhasedNP) :
    (license ds ls nps).ValuedLE (license ds ls' nps) := by
  suffices ∀ {s t : Valuation PhasedNP CaseValue}, s.ValuedLE t →
      (ds.foldl (fun st c ↦ cycle ls c st) s).ValuedLE (ds.foldl (fun st c ↦ cycle ls' c st) t)
    from this (.refl _)
  induction ds with
  | nil => exact id
  | cons c ds ih => exact fun hst ↦ ih (valuedLE_foldl_agree (h.filter _) hst)

theorem Converges.mono (hc : Converges ds ls nps) (h : ls <+ ls') : Converges ds ls' nps :=
  forall₂_trans (fun _ _ _ h₁ h₂ hn ↦ h₂.2 (h₁ hn)) hc (license_mono h ds _)

theorem converges_of_forall_needsLicensing_eq_false
    (h : ∀ np ∈ nps, np.needsLicensing = false) : Converges ds ls nps :=
  forall₂_iff_zip.2 ⟨by simp, fun hx hn ↦ by simp [h _ (of_mem_zip hx).1] at hn⟩

end Derivation

/-! ### The Licensing Economy Principle -/

section Economy

variable {ds : List Cat} {ls : List Licenser} {nps : List LicensedNP} {S : Finset Licenser}

/-- The licensers of a clause when the secondaries in `S` are activated: the obligatory ones
and the activated ones, in place. -/
def activate (ls : List Licenser) (S : Finset Licenser) : List Licenser :=
  ls.filter fun l ↦ decide (l.kind = .obligatory ∨ l ∈ S)

/-- An activation is economical iff it converges and no activation of fewer licensers does: the
derivation with fewer licensers is preferred. -/
def Economical (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP)
    (S : Finset Licenser) : Prop :=
  Minimal (fun S ↦ Converges ds (activate ls S) nps) S

theorem activate_sublist (ls : List Licenser) (S : Finset Licenser) : activate ls S <+ ls :=
  filter_sublist

theorem monotone_converges_activate (ds : List Cat) (ls : List Licenser)
    (nps : List LicensedNP) : Monotone fun S ↦ Converges ds (activate ls S) nps :=
  fun _ _ hS hc ↦ hc.mono <| monotone_filter_right _ fun _ ↦ by simpa using Or.imp_right (@hS _)

/-- An activation is economical iff it converges and no activated secondary licenser can be dropped,
the Licensing Economy Principle ((36) of [kalin-2018]). -/
theorem economical_iff : Economical ds ls nps S ↔
    Converges ds (activate ls S) nps ∧ ∀ l ∈ S, ¬ Converges ds (activate ls (S.erase l)) nps :=
  Finset.minimal_iff_forall_erase fun _ _ h hts ↦ monotone_converges_activate ds ls nps hts h

instance : Decidable (Economical ds ls nps S) := decidable_of_iff' _ economical_iff

theorem Economical.mem (h : Economical ds ls nps S) {l : Licenser} (hl : l ∈ S) :
    l ∈ ls ∧ l.kind = .secondary := by
  rw [economical_iff] at h
  by_contra hs
  have he : activate ls (S.erase l) = activate ls S := filter_congr fun x hx ↦ by
    by_cases hxl : x = l
    · subst hxl
      cases hk : x.kind <;> simp_all
    · simp [hxl]
  exact h.2 l hl (he ▸ h.1)

theorem Economical.subset_toFinset (h : Economical ds ls nps S) : S ⊆ ls.toFinset :=
  fun _ hl ↦ mem_toFinset.2 (h.mem hl).1

theorem exists_economical_iff : (∃ S, Economical ds ls nps S) ↔ Converges ds ls nps := by
  refine ⟨fun ⟨S, h⟩ ↦ (Minimal.prop h).mono (activate_sublist _ _), fun h ↦ ?_⟩
  refine exists_minimal_of_wellFoundedLT _ ⟨ls.toFinset, ?_⟩
  rwa [activate, filter_eq_self.2 fun l hl ↦ by simp [mem_toFinset.2 hl]]

theorem Economical.eq_empty (h : Economical ds ls nps S)
    (h₀ : Converges ds (activate ls ∅) nps) : S = ∅ :=
  (Minimal.eq_of_le h h₀ (Finset.empty_subset S)).symm

theorem Economical.not_isDOMMarked (h : Economical ds ls nps S)
    (h₀ : Converges ds (activate ls ∅) nps) :
    ∀ p ∈ license ds (activate ls S) (nps.map (·.toPhasedNP)), ¬ IsDOMMarked p.2 := by
  rintro ⟨np, _ | _ | l⟩ hp hdom <;> simp only [IsDOMMarked] at hdom
  have hl := mem_of_mem_license hp
  simp [h.eq_empty h₀, activate, hdom] at hl

end Economy

/-! ### Licensing as the Agree modality of case assignment -/

/-- The case and mechanism a Case value amounts to: the lexical case, or under Agree the case
`κ` gives the licensing head. -/
def CaseValue.assigned (κ : Cat → _root_.Case) :
    CaseValue → _root_.Case × _root_.Case.Mechanism
  | .lexical c => (c, .lexical)
  | .licenser l => (κ l.head, .agree)

private theorem rules_eq_of (g : CaseAssigners) (hg : ∀ d ∈ g.domains, d.2 = {}) (c : Cat) :
    g.rules c = {} := by
  unfold CaseAssigners.rules
  rcases hf : g.domains.find? (·.1 == c) with _ | d
  · rw [hf]; rfl
  · rw [hf]; exact hg d (mem_of_find?_eq_some hf)

theorem assign_eq_map_license (g : CaseAssigners)
    (hg : ∀ d ∈ g.domains, d.2 = {}) (κ : Cat → _root_.Case) {ls : List Licenser}
    (hκ : ∀ l ∈ ls, g.agreeCase l.head = some (κ l.head)) (nps : List PhasedNP) :
    g.assign id (ls.map fun l ↦ (l.head, l.domain)) nps =
      (license (g.domains.map (·.1)) ls nps).map
        (Prod.map id (Option.map (CaseValue.assigned κ))) := by
  set φ : PhasedNP × Option CaseValue → PhasedNP × Option (_root_.Case × _root_.Case.Mechanism) :=
    Prod.map id (Option.map (CaseValue.assigned κ))
  have key (c : Cat) (L : List Licenser)
      (hL : ∀ l ∈ L, l.domain = c ∧ g.agreeCase l.head = some (κ l.head))
      (st : Valuation PhasedNP CaseValue) :
      L.foldl (fun st l ↦ probePass g id c l.head st) (st.map φ) =
        (L.foldl (fun st l ↦ l.agree st) st).map φ := by
    induction L generalizing st with
    | nil => rfl
    | cons l L ih =>
      obtain ⟨hdom, hcase⟩ := hL l (mem_cons_self ..)
      have hstep : probePass g id c l.head (st.map φ) = (l.agree st).map φ := by
        simp only [probePass, hcase, Licenser.agree, hdom]
        exact agreeValue_map (P := (·.visible c)) (P' := (·.visible c)) (v := .licenser l)
          id (CaseValue.assigned κ) (fun _ ↦ rfl) rfl st
      rw [foldl_cons, foldl_cons, hstep, ih (fun l hl ↦ hL l (mem_cons_of_mem _ hl))]
  have hcycle (c : Cat) (st : Valuation PhasedNP CaseValue) :
      domainPass g id (ls.map fun l ↦ (l.head, l.domain)) c (st.map φ) = (cycle ls c st).map φ := by
    rw [domainPass, rules_eq_of g hg, DependentCase.Rules.unmarkedPass_of_none _ _ rfl,
      DependentCase.Rules.dependentPass_of_none _ _ rfl rfl, filter_map, foldl_map, cycle]
    exact key c _ (fun l hl ↦ by
      obtain ⟨hl, hc⟩ := mem_filter.1 hl
      exact ⟨by simpa using hc, hκ l hl⟩) st
  have hinit : _root_.Case.lexicalValuation (fun x ↦ (id x).lexicalCase) nps =
      (initial nps).map φ := by
    simp [_root_.Case.lexicalValuation, initial, Valuation.initial, φ, Option.map_map,
      Function.comp_def, CaseValue.assigned]
  rw [CaseAssigners.assign, CaseAssigners.derive, license, hinit]
  suffices ∀ st : Valuation PhasedNP CaseValue, (g.domains.map (·.1)).foldl
      (fun st c ↦ domainPass g id (ls.map fun l ↦ (l.head, l.domain)) c st) (st.map φ) =
      ((g.domains.map (·.1)).foldl (fun st c ↦ cycle ls c st) st).map φ by
    exact this _
  intro st
  induction g.domains.map (·.1) generalizing st with
  | nil => rfl
  | cons c ds ih => rw [foldl_cons, foldl_cons, hcycle, ih]

end Licensing

/-! ### Senaya's licensers -/

/-- Imperfective Asp, the obligatory licenser of the imperfective, (43). -/
def aspImpf : Licenser := { head := .Asp, kind := .obligatory }

/-- The T selecting imperfective Asp, a secondary licenser, (43). -/
def tImpf : Licenser := { head := .T, kind := .secondary }

/-- The T selecting perfective Asp, the one obligatory licenser of the perfective, (49). -/
def tPfv : Licenser := { head := .T, kind := .obligatory }

/-- The imperfective's licensers in merge order: Asp, then T. -/
def imperfective : List Licenser := [aspImpf, tImpf]

/-- The perfective's licenser: T alone. -/
def perfective : List Licenser := [tPfv]

/-- The one phase domain of a Senaya clause, v being no phase head. -/
def domains : List Cat := [.C]

/-- The agreement suffix a licensing head yields, an S-suffix from Asp and an L-suffix from T. -/
inductive Suffix
  | S
  | L
  deriving DecidableEq, Repr

/-- The suffix agreement with a head yields. -/
def headSuffix : Cat → Option Suffix
  | .Asp => some .S
  | .T => some .L
  | _ => none

/-- The suffix of a nominal's Case value: that of the head that licensed it, if any. -/
def suffixOf : Option CaseValue → Option Suffix
  | some (.licenser l) => headSuffix l.head
  | _ => none

/-- A Senaya nominal, which needs licensing exactly when specific, (40) to (42). -/
def nominal (specific : Bool) : LicensedNP := { needsLicensing := specific }

/-- A transitive clause's subject and object. -/
def transitive (subject object : Bool) : List LicensedNP :=
  [nominal subject, nominal object]

/-! ### The agreement data (Section 2.1) -/

/-- A row carries the aspect's licensers, the object if any, the subject's and the object's
suffix, and the judgment. -/
structure Row where
  clause : List Licenser
  object : Option Bool
  subjectSuffix : Suffix
  objectSuffix : Option Suffix
  grammatical : Bool

/-- A suffix feature value. -/
def suffixFeature : String → Option (Option Suffix)
  | "S" => some (some .S)
  | "L" => some (some .L)
  | "none" => some none
  | _ => none

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let cl ← match e.feature? "aspect" with
    | some "imperfective" => some imperfective
    | some "perfective" => some perfective
    | _ => none
  let obj ← match e.feature? "object" with
    | some "specific" => some (some true)
    | some "nonspecific" => some (some false)
    | some "none" => some none
    | _ => none
  let s ← (e.feature? "subject_suffix").bind suffixFeature
  let s ← s
  let o ← (e.feature? "object_suffix").bind suffixFeature
  some ⟨cl, obj, s, o, e.judgment = .acceptable⟩

/-- The Senaya data, (8) to (12) and (38). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The nominals of a row: a subject of the given specificity, and the row's object if any. -/
def Row.nominals (r : Row) (subject : Bool) : List LicensedNP :=
  nominal subject :: (r.object.map nominal).toList

/-- The suffixes of a row: the subject's, then the object's if there is an object. -/
def Row.suffixes (r : Row) : List (Option Suffix) :=
  some r.subjectSuffix :: (r.object.map fun _ ↦ r.objectSuffix).toList

/-- The suffixes a derivation spells out, nominal by nominal. -/
def suffixes (st : Valuation PhasedNP CaseValue) : List (Option Suffix) :=
  st.map (suffixOf ·.2)

private theorem rows_agree_aux : ∀ r ∈ rows, ∀ subject : Bool,
    (r.grammatical = true ↔ Converges domains r.clause (r.nominals subject)) ∧
    ∀ S ∈ r.clause.toFinset.powerset, Economical domains r.clause (r.nominals subject) S →
      suffixes (license domains (activate r.clause S)
        ((r.nominals subject).map (·.toPhasedNP))) = r.suffixes := by
  decide

theorem rows_agree : ∀ r ∈ rows, ∀ subject : Bool,
    (r.grammatical = true ↔ ∃ S, Economical domains r.clause (r.nominals subject) S) ∧
    ∀ S, Economical domains r.clause (r.nominals subject) S →
      suffixes (license domains (activate r.clause S)
        ((r.nominals subject).map (·.toPhasedNP))) = r.suffixes := by
  intro r hr subject
  obtain ⟨h₁, h₂⟩ := rows_agree_aux r hr subject
  exact ⟨h₁.trans exists_economical_iff.symm,
    fun S hS ↦ h₂ S (Finset.mem_powerset.2 hS.subset_toFinset) hS⟩

/-- In the imperfective a specific object is licensed by the secondary T (47), and a nonspecific one
activates nothing and goes unlicensed (48). -/
theorem imperfective_object (subject : Bool) :
    Economical domains imperfective (transitive subject true) {tImpf} ∧
      (license domains (activate imperfective {tImpf})
        ((transitive subject true).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser aspImpf), some (.licenser tImpf)] ∧
    Economical domains imperfective (transitive subject false) ∅ ∧
      (license domains (activate imperfective ∅)
        ((transitive subject false).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser aspImpf), none] := by
  cases subject <;> decide

/-! ### The toy language of Section 3.1 -/

/-- Finite T, the obligatory licenser of the toy language. -/
def toyT : Licenser := { head := .T, kind := .obligatory }

/-- v, a secondary licenser probing its own domain. -/
def toyV : Licenser := { head := .v, domain := .v, kind := .secondary }

/-- The toy language's licensers. -/
def toy : List Licenser := [toyV, toyT]

/-- The toy language's phase domains, v's spelling out before C's. -/
def toyDomains : List Cat := [.v, .C]

/-- A transitive clause of the toy language, in which a nominal needs licensing exactly when
animate: the subject above v, the object in its domain. -/
def toyTransitive (subject object : Bool) : List LicensedNP :=
  [{ needsLicensing := subject }, { phase := .v, needsLicensing := object }]

/-- An animate object activates v, without which the derivation crashes (24). -/
theorem toy_animate_object (subject : Bool) :
    ¬ Converges toyDomains (activate toy ∅) (toyTransitive subject true) ∧
    Economical toyDomains toy (toyTransitive subject true) {toyV} ∧
      (license toyDomains toy ((toyTransitive subject true).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser toyT), some (.licenser toyV)] := by
  cases subject <;> decide

/-- An inanimate object activates nothing and goes unlicensed and unmarked, (23). -/
theorem toy_inanimate_object (subject : Bool) :
    Economical toyDomains toy (toyTransitive subject false) ∅ ∧
      (license toyDomains (activate toy ∅)
        ((toyTransitive subject false).map (·.toPhasedNP))).map (·.2) =
        [some (.licenser toyT), none] := by
  cases subject <;> decide

/-! ### Licensing against dependent case -/

/-- Dependent case values a specific perfective object accusative, but licensing leaves it unvalued
and the derivation crashes (Section 2.1.3). -/
theorem dependentCase_values_banned_object (subject : Bool) :
    ((DependentCase.assignCases .accusative (·.lexicalCase) (transitive subject true))[1]?.bind
        (·.2.map (·.1))) = some .acc ∧
    ¬ Converges domains perfective (transitive subject true) := by
  cases subject <;> decide

end Kalin2018
