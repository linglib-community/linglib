module

public import Linglib.Semantics.Dynamic.PCDRT

/-!
# Partial Plural CDRT

Haug and Dalrymple's Partial Plural Compositional DRT joins the plural information states of
Plural CDRT (Brasoveanu, Dotlačil) with the partial assignments of Partial CDRT
(Haug), in which an anaphoric condition is a presupposition rather than a resolution the
grammar makes. This file defines the conditions of a PPDRS on the states of `PCDRT`, reading a
dref's values and dependencies through `PCDRT.value` and `PCDRT.dep`.

A condition takes the output state and the set `Δ` of drefs the DRS distributes over. Three
anaphoric relations are distinguished, after Higginbotham and Williams:

* binding (`u_anaph = u_ant`), pointwise equality of the two drefs, which needs c-command;
* group identity (`∪u_anaph → ∪u_ant`), the anaphor's values summed over each state's class
  under distribution equal to the antecedent's values over the whole state, so that the
  antecedent escapes the distribution;
* reciprocity, group identity with distinctness in every state, the contribution of *each
  other*; without the distinctness it is the underspecified meaning of German *sich* or the
  Cheyenne reflexive/reciprocal affix (Murray, Cable).

## Main definitions

* `PPCDRT.PPDRSCond`: a condition on a plural state under a distribution context.
* `PPCDRT.eqClass`: the class of a state under distribution.
* `PPCDRT.bindingCond`, `PPCDRT.groupIdentityCond`, `PPCDRT.reciprocityCond`,
  `PPCDRT.underspecifiedCond`: the anaphoric relations.
* `PPCDRT.extend`, `PPCDRT.introPartial`: partial dref introduction on assignments and on plural
  states.

## Main results

* `PPCDRT.groupIdentityCond_empty`: without distribution, group identity is equality of the two
  drefs' values.
* `PPCDRT.reciprocityCond_empty_iff`: without distribution, reciprocity is a dependency with equal
  domain and codomain and no reflexive pair.
* `PPCDRT.binding_implies_groupIdentity`, `PPCDRT.reciprocity_excludes_binding`: binding and
  reciprocity against group identity.
* `PPCDRT.nontrivial_value_of_reciprocityCond`: a reciprocal's antecedent denotes a plurality.
* `PPCDRT.mem_extend_iff_covBy`: introducing a dref is a covering step of the extension order.
* `PPCDRT.introPartial_subset_intro`: partial introduction refines Plural CDRT's.

## References

* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [D. T. T. Haug, *Partial dynamic semantics for anaphora: Compositionality without syntactic
  coindexation* (2014)][haug-2014]
* [A. Brasoveanu, *Structured nominal and modal reference* (2007)][brasoveanu-2007]
* [J. Dotlačil, *Reciprocals distribute over information states* (2013)][dotlacil-2013]
* [J. Higginbotham, *On semantics* (1985)][higginbotham-1985]
* [E. Williams, *Reciprocal scope* (1991)][williams-1991]
* [S. E. Murray, *Reflexivity and reciprocity with(out) underspecification* (2008)][murray-2008]
* [S. Cable, *Reflexives, reciprocals and contrast* (2014)][cable-2014]
-/

@[expose] public section

namespace PPCDRT

open PCDRT

variable {E : Type*}

/-- A PPDRS condition ([haug-dalrymple-2020] (27)): a property of the output plural state and of
the set `Δ` of drefs the DRS distributes over ((25)). -/
abbrev PPDRSCond (E : Type*) := PluralAssign ℕ E → Set ℕ → Prop

variable (uAnaph uAnt : ℕ) (S : PluralAssign ℕ E) (Δ : Set ℕ)

/-! ### Distribution -/

/-- The class of `s` under distribution over `Δ` ([haug-dalrymple-2020] (26)): the states of `S`
agreeing with `s` on every dref in `Δ`. -/
def eqClass (s : PartialAssign ℕ E) : PluralAssign ℕ E :=
  {t ∈ S | ∀ u ∈ Δ, t u = s u}

@[simp] theorem eqClass_empty (s : PartialAssign ℕ E) : eqClass S ∅ s = S := by
  ext t; simp [eqClass]

theorem mem_eqClass {s t : PartialAssign ℕ E} :
    t ∈ eqClass S Δ s ↔ t ∈ S ∧ ∀ u ∈ Δ, t u = s u := Iff.rfl

theorem self_mem_eqClass {s : PartialAssign ℕ E} (hs : s ∈ S) : s ∈ eqClass S Δ s :=
  ⟨hs, fun _ _ ↦ rfl⟩

/-! ### Anaphoric relations -/

/-- Binding (`u_anaph = u_ant`, [haug-dalrymple-2020] (30)): the two drefs hold the same value in
every state, both defined and equal or both undefined. This is stronger than the coreference
presupposition of (29), which constrains only the states where both are defined. -/
def bindingCond : PPDRSCond E := fun S _ ↦ ∀ s ∈ S, s uAnaph = s uAnt

/-- Group identity (`∪u_anaph → ∪u_ant`, [haug-dalrymple-2020] (29), (38)): in every state, the
anaphor's values over the state's class under distribution are the antecedent's values over the
whole state. -/
def groupIdentityCond : PPDRSCond E := fun S Δ ↦
  ∀ s ∈ S, value uAnaph (eqClass S Δ s) = value uAnt S

/-- Reciprocity (`∪u_anaph → ∪u_ant`, `∂(u_anaph ≠ u_ant)`, [haug-dalrymple-2020] (41)): group
identity, with the two drefs distinct in every state where both are defined. -/
def reciprocityCond : PPDRSCond E := fun S Δ ↦
  groupIdentityCond uAnaph uAnt S Δ ∧
    ∀ s ∈ S, ∀ a b : E, s uAnaph = ↑a → s uAnt = ↑b → a ≠ b

/-- The underspecified reflexive/reciprocal ([haug-dalrymple-2020] (79b)): group identity
without distinctness, admitting reflexive, reciprocal and mixed construals ([murray-2008],
[cable-2014]). -/
def underspecifiedCond : PPDRSCond E := groupIdentityCond uAnaph uAnt

/-- Without distribution, group identity is equality of the two drefs' values, the cumulative
identity `∪u_anaph = ∪u_ant` of [haug-dalrymple-2020] (39). -/
theorem groupIdentityCond_empty :
    groupIdentityCond uAnaph uAnt S ∅ ↔ value uAnaph S = value uAnt S := by
  simp only [groupIdentityCond, eqClass_empty]
  refine ⟨fun h ↦ ?_, fun h _ _ ↦ h⟩
  obtain rfl | ⟨s, hs⟩ := S.eq_empty_or_nonempty
  · simp [value]
  · exact h s hs

/-- Binding implies group identity without distribution. Under distribution the two come apart
([haug-dalrymple-2020] (24) against (31)). -/
theorem binding_implies_groupIdentity (h : bindingCond uAnaph uAnt S ∅) :
    groupIdentityCond uAnaph uAnt S ∅ := by
  intro s hs
  rw [eqClass_empty]
  exact Set.ext fun _ ↦ exists_congr fun g ↦ and_congr_right fun hg ↦ by
    change g uAnaph = _ ↔ g uAnt = _
    rw [h g hg]

/-- Reciprocity excludes binding once some state defines the anaphor: distinctness there
contradicts pointwise equality. Without such a state both drefs may be undefined throughout, and
binding and reciprocity hold together vacuously. -/
theorem reciprocity_excludes_binding (hdef : ∃ s ∈ S, ∃ d : E, s uAnaph = ↑d)
    (h : reciprocityCond uAnaph uAnt S Δ) : ¬ bindingCond uAnaph uAnt S Δ := fun hb ↦
  let ⟨s, hs, d, hd⟩ := hdef
  h.2 s hs d d hd ((hb s hs).symm.trans hd) rfl

theorem reciprocity_strengthens_underspecified (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ := h.1

variable {uAnaph uAnt S Δ}

/-- Without distribution, reciprocity says the antecedent-anaphor dependency is irreflexive with
equal domain and codomain ([haug-dalrymple-2020]'s gloss of (39)). -/
theorem reciprocityCond_empty_iff (hdef : ∀ s ∈ S, s uAnaph ≠ ⊥ ↔ s uAnt ≠ ⊥) :
    reciprocityCond uAnaph uAnt S ∅ ↔
      (dep uAnt uAnaph S).dom = (dep uAnt uAnaph S).cod ∧ (dep uAnt uAnaph S).IsIrrefl := by
  rw [reciprocityCond, groupIdentityCond_empty,
    ← dom_dep (u := uAnt) (v := uAnaph) fun s hs ↦ (hdef s hs).2,
    ← cod_dep (u := uAnt) (v := uAnaph) fun s hs ↦ (hdef s hs).1, eq_comm]
  refine and_congr_right' ⟨fun h ↦ ⟨fun a ⟨s, hs, ha, ha'⟩ ↦ h s hs a a ha' ha rfl⟩, ?_⟩
  rintro h s hs a b ha hb rfl
  exact h.irrefl _ ⟨s, hs, hb, ha⟩

/-- A reciprocal's antecedent denotes a plurality: at a state defining both drefs, the
anaphor's value lies among the antecedent's by group identity and differs from the antecedent's
value there. This holds under any distribution. -/
theorem nontrivial_value_of_reciprocityCond (h : reciprocityCond uAnaph uAnt S Δ)
    {s : PartialAssign ℕ E} (hs : s ∈ S) {a b : E} (ha : s uAnaph = ↑a)
    (hb : s uAnt = ↑b) : (value uAnt S).Nontrivial :=
  ⟨a, h.1 s hs ▸ ⟨s, self_mem_eqClass S Δ hs, ha⟩, b, ⟨s, hs, hb⟩, h.2 s hs a b ha hb⟩

/-! ### Partial dref introduction -/

section Introduction

open DynamicSemantics SetRel

variable {Var D : Type*} {u : Var} {i o : PartialAssign Var D}

/-- Partial dref introduction `i[u]o` ([haug-dalrymple-2020] (20)): `i` leaves `u` unvalued, `o`
values it, and the two agree on every other dref. -/
def extend (u : Var) : Update (PartialAssign Var D) :=
  {p | p.1 u = ⊥ ∧ p.2 u ≠ ⊥ ∧ ∀ v ≠ u, p.1 v = p.2 v}

theorem mem_extend : i ~[extend u] o ↔ i u = ⊥ ∧ o u ≠ ⊥ ∧ ∀ v ≠ u, i v = o v :=
  Iff.rfl

/-- Introducing `u` is a covering step of the extension order, the one that values `u`. -/
theorem mem_extend_iff_covBy : i ~[extend u] o ↔ i ⋖ o ∧ i u ≠ o u := by
  refine ⟨fun ⟨hi, ho, h⟩ ↦ ⟨PartialAssign.covBy_iff.2 ⟨u, hi, ho, h⟩,
    fun he ↦ ho (he.symm.trans hi)⟩,
    fun ⟨hcov, hne⟩ ↦ ?_⟩
  obtain ⟨x, hi, ho, h⟩ := PartialAssign.covBy_iff.1 hcov
  obtain rfl : x = u := by_contra fun hxu ↦ hne (h u (Ne.symm hxu))
  exact ⟨hi, ho, h⟩

theorem extend_subset_randomAssign [DecidableEq Var] :
    extend u ⊆ Update.randomAssign (S := PartialAssign Var D) u := by
  rintro ⟨i, o⟩ ⟨-, -, h⟩
  refine (Update.mem_randomAssign (i := i) (j := o) (r := u)).2 ⟨o u, funext fun v ↦ ?_⟩
  rw [RegisterStructure.extend_eq_update]
  by_cases hv : v = u
  · subst hv
    simp
  · rw [Function.update_of_ne hv]
    exact (h v hv).symm

/-- Partial dref introduction on plural states ([haug-dalrymple-2020] (6), after
[dotlacil-2013]): every input row has an extension at `u` among the output rows, every output row
extends some input row, and the output state is nonempty. It refines Plural CDRT's `PCDRT.intro`
(`introPartial_subset_intro`) in two ways: every output row values `u`, where a random assignment
may leave it ★, and the output is nonempty. -/
def introPartial (u : Var) : Update (PluralAssign Var D) :=
  {p | p.2.Nonempty ∧ p ∈ Update.cumul (extend u)}

theorem introPartial_subset_intro [DecidableEq Var] :
    introPartial u ⊆ PCDRT.intro (S := PartialAssign Var D) (V := Flat D) u :=
  fun _ hp ↦ Update.cumul_mono extend_subset_randomAssign hp.2

end Introduction

end PPCDRT
