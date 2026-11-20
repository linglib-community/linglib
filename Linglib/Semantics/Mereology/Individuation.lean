module

public import Mathlib.Order.Zorn
public import Linglib.Semantics.Mereology.Basic

/-!
# Individuation perspectives

A set of individuals is disjoint if no two distinct members overlap, mathlib's
`Set.PairwiseDisjoint`. A maximal disjoint subset `D` of a set `P` is an individuation
perspective on `P`, a way of counting its members ([landman-2011], [landman-2020]). Every member
of `P` lies in one (`Mereology.exists_isMaxDisjointIn_mem`). A disjoint set is its own only
perspective (`Mereology.isMaxDisjointIn_iff_eq`), and a set with two perspectives is not
disjoint (`Mereology.IsMaxDisjointIn.not_pairwiseDisjoint`).

## References

* [landman-2011], [landman-2020], [sutton-filip-2021]
-/

@[expose] public section

namespace Mereology

open Set

variable {α : Type*} [PartialOrder α] [OrderBot α] {P Q D D₁ D₂ : Set α} {x : α}

theorem not_pairwiseDisjoint_iff :
    ¬ P.PairwiseDisjoint id ↔ ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ¬ Disjoint x y := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]

instance [Fintype α] [DecidableEq α] [DecidableRel (Disjoint (α := α))]
    [DecidablePred (· ∈ P)] : Decidable (P.PairwiseDisjoint id) :=
  decidable_of_iff (∀ x, x ∈ P → ∀ y, y ∈ P → x ≠ y → Disjoint x y) Iff.rfl

/-! ### Perspectives -/

/-- `D` is a maximal disjoint subset of `P`, an individuation perspective on `P`. -/
def IsMaxDisjointIn (D P : Set α) : Prop := Maximal (fun D ↦ D ⊆ P ∧ D.PairwiseDisjoint id) D

theorem IsMaxDisjointIn.subset (h : IsMaxDisjointIn D P) : D ⊆ P := h.prop.1

theorem IsMaxDisjointIn.pairwiseDisjoint (h : IsMaxDisjointIn D P) : D.PairwiseDisjoint id :=
  h.prop.2

/-- A disjoint subset is maximal when no member of the predicate can be added to it without
overlap. -/
theorem isMaxDisjointIn_iff :
    IsMaxDisjointIn D P ↔
      D ⊆ P ∧ D.PairwiseDisjoint id ∧ ∀ x ∈ P, x ∉ D → ¬ (insert x D).PairwiseDisjoint id :=
  ⟨fun h ↦ ⟨h.subset, h.pairwiseDisjoint, fun x hx hxD hd ↦
      hxD (h.2 ⟨insert_subset hx h.subset, hd⟩ (subset_insert x D) (mem_insert x D))⟩,
    fun ⟨hDP, hD, hmax⟩ ↦ ⟨⟨hDP, hD⟩, fun _ hD' hDD' x hx ↦ by_contra fun hxD ↦
      hmax x (hD'.1 hx) hxD (hD'.2.subset (insert_subset hx hDD'))⟩⟩

instance [Fintype α] [DecidableEq α] [DecidableRel (Disjoint (α := α))] [DecidablePred (· ∈ D)]
    [DecidablePred (· ∈ P)] : Decidable (IsMaxDisjointIn D P) :=
  haveI (x : α) : DecidablePred (· ∈ insert x D) := fun y ↦
    decidable_of_iff (y = x ∨ y ∈ D) Iff.rfl
  decidable_of_iff ((∀ x, x ∈ D → x ∈ P) ∧ D.PairwiseDisjoint id ∧
    ∀ x, x ∈ P → x ∉ D → ¬ (insert x D).PairwiseDisjoint id) isMaxDisjointIn_iff.symm

/-- Every member of a predicate lies in a perspective on it. -/
theorem exists_isMaxDisjointIn_mem (hx : x ∈ P) : ∃ D, IsMaxDisjointIn D P ∧ x ∈ D := by
  obtain ⟨D, hxD, hD⟩ := zorn_subset_nonempty {D | D ⊆ P ∧ D.PairwiseDisjoint id}
    (fun c hc hchain _ ↦ ⟨⋃₀ c, ⟨sUnion_subset fun D hD ↦ (hc hD).1,
      (pairwise_sUnion hchain.directedOn).2 fun D hD ↦ (hc hD).2⟩,
      fun D hD ↦ subset_sUnion_of_mem hD⟩)
    {x} ⟨singleton_subset_iff.2 hx, pairwiseDisjoint_singleton x id⟩
  exact ⟨D, hD, hxD rfl⟩

/-- The union of two distinct perspectives is not disjoint. -/
theorem IsMaxDisjointIn.not_pairwiseDisjoint_union (h₁ : IsMaxDisjointIn D₁ P)
    (h₂ : IsMaxDisjointIn D₂ P) (hne : D₁ ≠ D₂) : ¬ (D₁ ∪ D₂).PairwiseDisjoint id := fun h ↦
  have hP : D₁ ∪ D₂ ⊆ P ∧ (D₁ ∪ D₂).PairwiseDisjoint id := ⟨union_subset h₁.subset h₂.subset, h⟩
  hne ((subset_union_left.trans (h₂.2 hP subset_union_right)).antisymm
    (subset_union_right.trans (h₁.2 hP subset_union_left)))

/-- A predicate with two distinct perspectives is not disjoint. -/
theorem IsMaxDisjointIn.not_pairwiseDisjoint (h₁ : IsMaxDisjointIn D₁ P)
    (h₂ : IsMaxDisjointIn D₂ P) (hne : D₁ ≠ D₂) : ¬ P.PairwiseDisjoint id := fun h ↦
  h₁.not_pairwiseDisjoint_union h₂ hne (h.subset (union_subset h₁.subset h₂.subset))

/-- A disjoint predicate is its own only perspective. -/
theorem isMaxDisjointIn_iff_eq (h : P.PairwiseDisjoint id) :
    IsMaxDisjointIn D P ↔ D = P :=
  ⟨fun hD ↦ hD.subset.antisymm (hD.2 ⟨Subset.rfl, h⟩ hD.subset),
    by rintro rfl; exact ⟨⟨Subset.rfl, h⟩, fun _ hD' _ ↦ hD'.1⟩⟩

theorem isMaxDisjointIn_self (h : P.PairwiseDisjoint id) : IsMaxDisjointIn P P :=
  (isMaxDisjointIn_iff_eq h).2 rfl

end Mereology
