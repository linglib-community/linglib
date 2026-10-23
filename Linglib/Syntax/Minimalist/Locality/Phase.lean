/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Phases

The phases of [marcolli-chomsky-berwick-2025] §1.14, after [chomsky-2013], with the raising head
`SyntacticObject.raisingHead` as head function. A lexical item heads a phase when it projects, and
its complement is the sister it projects over. The phase is what lies within the terms the head
heads; its interior is what lies within the complement; and its edge is the rest of the phase, the
head and what is merged above it, a phrase raised to the edge included. The Phase
Impenetrability Condition seals the interior: under [chomsky-2000]'s condition to everything
outside the phase, under [chomsky-2001]'s only once the next phase head up is merged, to what lies
outside its interior.

## Main definitions

* `SyntacticObject.IsPhaseHead`, `SyntacticObject.IsComplementOf`: a lexical item projects, and
  the sister it projects over.
* `SyntacticObject.WithinProjection`, `SyntacticObject.WithinComplement`: a term lies within the
  projection or the complement of a head.
* `SyntacticObject.phase`, `SyntacticObject.phaseInterior`, `SyntacticObject.phaseEdge`: the
  phase of a head, its interior, and its edge.
* `Impenetrability`, `SyntacticObject.Accessible`: the two conditions, and the goals each leaves
  accessible to a probe.

## Main statements

* `SyntacticObject.isPhaseHead_iff_phaseInterior_ne_zero`: a head projects exactly when its phase
  has a nonempty interior.
* `SyntacticObject.phaseInterior_add_phaseEdge`: the interior and the edge partition the phase.
* `SyntacticObject.phaseInterior_eq_cCommandDomain`: the interior of a head that projects
  wherever it occurs is its c-command domain.
* `SyntacticObject.Accessible.nextPhase_of_phase`: [chomsky-2000]'s condition is the stronger.

## Implementation notes

* Terms are values, not occurrences, so all copies of a head share one phase, and the lower
  copies of a moved phrase are one term; positions tell copies apart in
  `Copy/Chain.lean`.
* Every head that projects heads a phase, as in the book; the heads a study counts as phase heads
  (C alone, or also v, D, or Voice) are the list `Accessible` takes.
* Under the raising head a phrase raised to the edge of a head lies in its phase; a phrase merged
  there in place lies in it only when the head selects it.

## TODO

* The terms made inaccessible by the interiors of lower phases, and the stricter variant that
  also freezes their heads.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-2013]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Minimalist

/-- When the Phase Impenetrability Condition seals the interior of a phase head. -/
inductive Impenetrability
  /-- Once the phase is built, to everything outside it ([chomsky-2000]). -/
  | phase
  /-- Once the next phase head up is merged, to everything outside its interior
  ([chomsky-2001]). -/
  | nextPhase
  deriving DecidableEq, Repr

namespace SyntacticObject

open Relation

variable (T : SyntacticObject) (ℓ : LexicalItem.Token) (x z : SyntacticObject)

/-- `ℓ` heads a phase of `T` when it projects, heading a mother of its leaf. -/
def IsPhaseHead : Prop := ∃ m ∈ T.terms, m.raisingHead = some ℓ ∧ ImmediatelyContains m (leaf ℓ)

instance : Decidable (IsPhaseHead T ℓ) := Multiset.decidableExistsMultiset

/-- `z` is the complement of `ℓ` in `T` when `ℓ` projects over its sister `z`. -/
def IsComplementOf : Prop :=
  ∃ m ∈ T.terms, m.raisingHead = some ℓ ∧ ImmediatelyContains m (leaf ℓ) ∧
    ImmediatelyContains m z ∧ z ≠ leaf ℓ

instance : Decidable (IsComplementOf T ℓ z) := Multiset.decidableExistsMultiset

/-- `x` lies within the projection of `ℓ` in `T` when a term of `T` that `ℓ` heads contains it. -/
def WithinProjection : Prop := ∃ p ∈ T.terms, p.raisingHead = some ℓ ∧ ContainsOrEq p x

instance : Decidable (WithinProjection T ℓ x) := Multiset.decidableExistsMultiset

/-- `x` lies within the complement of `ℓ` in `T` when a complement of `ℓ` contains it. -/
def WithinComplement : Prop := ∃ z ∈ T.terms, IsComplementOf T ℓ z ∧ ContainsOrEq z x

instance : Decidable (WithinComplement T ℓ x) := Multiset.decidableExistsMultiset

/-- The phase of `ℓ` in `T` is the multiset of terms within its projection. -/
def phase : Multiset SyntacticObject := T.terms.filter (WithinProjection T ℓ)

/-- The interior of the phase of `ℓ` in `T` is the multiset of terms within its complement. -/
def phaseInterior : Multiset SyntacticObject := T.terms.filter (WithinComplement T ℓ)

/-- The edge of the phase of `ℓ` in `T` is the multiset of terms of the phase outside its
interior. -/
def phaseEdge : Multiset SyntacticObject := (T.phase ℓ).filter (· ∉ T.phaseInterior ℓ)

variable {T ℓ x z} {y : SyntacticObject}

theorem IsComplementOf.mem_terms (h : IsComplementOf T ℓ z) : z ∈ T.terms :=
  let ⟨_, hm, _, _, hz, _⟩ := h
  SyntacticObject.mem_terms.2 (.tail (SyntacticObject.mem_terms.1 hm) hz)

theorem WithinProjection.mem_terms (h : WithinProjection T ℓ x) : x ∈ T.terms :=
  let ⟨_, hp, _, hpx⟩ := h
  terms_subset_terms (SyntacticObject.mem_terms.1 hp) (SyntacticObject.mem_terms.2 hpx)

theorem WithinComplement.withinProjection (h : WithinComplement T ℓ x) : WithinProjection T ℓ x :=
  let ⟨_, _, ⟨m, hm, hℓ, _, hz, _⟩, hzx⟩ := h
  ⟨m, hm, hℓ, .head hz hzx⟩

theorem WithinComplement.mem_terms (h : WithinComplement T ℓ x) : x ∈ T.terms :=
  h.withinProjection.mem_terms

theorem WithinProjection.trans (hx : WithinProjection T ℓ x) (hxy : ContainsOrEq x y) :
    WithinProjection T ℓ y :=
  let ⟨p, hp, hℓ, hpx⟩ := hx
  ⟨p, hp, hℓ, hpx.trans hxy⟩

/-- Whatever a frozen term contains is frozen. -/
theorem WithinComplement.trans (hx : WithinComplement T ℓ x) (hxy : ContainsOrEq x y) :
    WithinComplement T ℓ y :=
  let ⟨z, hz, hc, hzx⟩ := hx
  ⟨z, hz, hc, hzx.trans hxy⟩

theorem WithinComplement.cCommands (h : WithinComplement T ℓ x) : T.CCommands (leaf ℓ) x :=
  let ⟨z, hz, ⟨m, hm, _, hmℓ, hmz, hne⟩, hzx⟩ := h
  ⟨z, hz, ⟨m, hm, hmℓ, hmz, hne.symm⟩, hzx⟩

@[simp] theorem mem_phase : x ∈ T.phase ℓ ↔ WithinProjection T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinProjection.mem_terms)

@[simp] theorem mem_phaseInterior : x ∈ T.phaseInterior ℓ ↔ WithinComplement T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinComplement.mem_terms)

@[simp] theorem mem_phaseEdge :
    x ∈ T.phaseEdge ℓ ↔ WithinProjection T ℓ x ∧ ¬ WithinComplement T ℓ x :=
  Multiset.mem_filter.trans (and_congr mem_phase (not_congr mem_phaseInterior))

theorem isPhaseHead_iff_exists_isComplementOf : IsPhaseHead T ℓ ↔ ∃ z, IsComplementOf T ℓ z := by
  refine ⟨fun ⟨m, hm, hℓ, hmℓ⟩ ↦ ?_, fun ⟨_, m, hm, hℓ, hmℓ, _⟩ ↦ ⟨m, hm, hℓ, hmℓ⟩⟩
  induction m using SyntacticObject.ind with
  | leaf => simp at hmℓ
  | trace => simp at hmℓ
  | traceOf => simp at hmℓ
  | merge l r _ _ =>
    rcases (immediatelyContains_merge _ _ _).1 hmℓ with rfl | rfl
    · exact ⟨r, _, hm, hℓ, by simp, by simp, by rintro rfl; simp at hℓ⟩
    · exact ⟨l, _, hm, hℓ, by simp, by simp, by rintro rfl; simp at hℓ⟩

theorem isPhaseHead_iff_phaseInterior_ne_zero : IsPhaseHead T ℓ ↔ T.phaseInterior ℓ ≠ 0 := by
  rw [isPhaseHead_iff_exists_isComplementOf]
  refine ⟨fun ⟨z, hz⟩ h0 ↦ Multiset.filter_eq_nil.1 h0 z hz.mem_terms ⟨z, hz.mem_terms, hz, .refl⟩,
    fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
  obtain ⟨z, -, hz, -⟩ := mem_phaseInterior.1 hx
  exact ⟨z, hz⟩

theorem phaseInterior_le_phase : T.phaseInterior ℓ ≤ T.phase ℓ :=
  Multiset.monotone_filter_right _ fun _ h ↦ h.withinProjection

theorem phaseInterior_add_phaseEdge : T.phaseInterior ℓ + T.phaseEdge ℓ = T.phase ℓ := by
  conv_rhs => rw [← Multiset.filter_add_not (· ∈ T.phaseInterior ℓ) (T.phase ℓ)]
  congr 1
  rw [phase, Multiset.filter_filter]
  exact Multiset.filter_congr fun _ _ ↦ by
    grind [mem_phaseInterior, WithinComplement.withinProjection]

theorem phaseInterior_le_cCommandDomain : T.phaseInterior ℓ ≤ T.cCommandDomain (leaf ℓ) :=
  Multiset.monotone_filter_right _ fun _ h ↦ h.cCommands

theorem phaseInterior_eq_cCommandDomain
    (h : ∀ m ∈ T.terms, ImmediatelyContains m (leaf ℓ) → m.raisingHead = some ℓ) :
    T.phaseInterior ℓ = T.cCommandDomain (leaf ℓ) :=
  Multiset.filter_congr fun _ _ ↦ by
    grind [WithinComplement, IsComplementOf, CCommands, Sisters]

/-! ### The Phase Impenetrability Condition -/

variable (T) in
/-- `goal` is accessible to `probe` in `T` under the condition `s`, the phase heads being `heads`:
a goal within the complement of a phase head is reachable only from within its phase, under
[chomsky-2001]'s condition only once a phase head above it is merged and the probe lies outside
that head's interior. -/
def Accessible (heads : List LexicalItem.Token) :
    Impenetrability → SyntacticObject → SyntacticObject → Prop
  | .phase, probe, goal => ∀ H ∈ heads, T.WithinComplement H goal → T.WithinProjection H probe
  | .nextPhase, probe, goal => ∀ H ∈ heads, T.WithinComplement H goal → ∀ Z ∈ heads, Z ≠ H →
      T.WithinProjection Z (leaf H) → ¬ T.WithinComplement Z probe → T.WithinProjection H probe

instance (heads : List LexicalItem.Token) (s : Impenetrability) (probe goal : SyntacticObject) :
    Decidable (T.Accessible heads s probe goal) := by
  cases s <;> dsimp only [Accessible] <;> infer_instance

/-- [chomsky-2000]'s condition is the stronger: what it leaves accessible, [chomsky-2001]'s does
too. -/
theorem Accessible.nextPhase_of_phase {heads : List LexicalItem.Token}
    {probe goal : SyntacticObject}
    (h : T.Accessible heads .phase probe goal) : T.Accessible heads .nextPhase probe goal :=
  fun H hH hg _ _ _ _ _ ↦ h H hH hg

end SyntacticObject

end Minimalist
