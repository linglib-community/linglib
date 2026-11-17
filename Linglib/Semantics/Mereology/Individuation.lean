module

public import Mathlib.Order.Zorn
public import Linglib.Semantics.Mereology.Basic

/-!
# Individuation perspectives

A set is disjoint if no two distinct members overlap. A maximal disjoint subset of a predicate is
an individuation perspective on it, a way of counting its members ([landman-2011],
[landman-2020]), and [every member lies in one](##Mereology.exists_isMaxDisjointIn_mem). A
disjoint predicate
[is its own only perspective](##Mereology.DisjointPred.isMaxDisjointIn_iff_eq), and a predicate
with [two perspectives is not disjoint](##Mereology.IsMaxDisjointIn.not_disjointPred).

## References

* [landman-2011], [landman-2020], [sutton-filip-2021]
-/

@[expose] public section

namespace Mereology

open Set

variable {α : Type*} [PartialOrder α] {P Q D D₁ D₂ : Set α} {x : α}

/-! ### Disjoint sets -/

/-- A set is disjoint if no two distinct members overlap. -/
def DisjointPred (P : Set α) : Prop := P.Pairwise fun x y ↦ ¬ Overlap x y

theorem not_disjointPred_iff : ¬ DisjointPred P ↔ ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ Overlap x y := by
  simp [DisjointPred, Set.Pairwise]

theorem DisjointPred.anti (h : P ⊆ Q) (hQ : DisjointPred Q) : DisjointPred P := hQ.mono h

@[simp]
theorem disjointPred_singleton (x : α) : DisjointPred {x} := pairwise_singleton x _

theorem disjointPred_iff_pairwiseDisjoint [OrderBot α] :
    DisjointPred P ↔ P.PairwiseDisjoint id := by
  simp only [DisjointPred, overlap_iff_not_disjoint, not_not]
  rfl

instance [Fintype α] [DecidableEq α] [DecidableRel (Overlap (α := α))]
    [DecidablePred (· ∈ P)] : Decidable (DisjointPred P) :=
  decidable_of_iff (∀ x, x ∈ P → ∀ y, y ∈ P → x ≠ y → ¬ Overlap x y) Iff.rfl

/-! ### Perspectives -/

/-- `D` is a maximal disjoint subset of `P`, an individuation perspective on `P`. -/
def IsMaxDisjointIn (D P : Set α) : Prop := Maximal (fun D ↦ D ⊆ P ∧ DisjointPred D) D

theorem IsMaxDisjointIn.subset (h : IsMaxDisjointIn D P) : D ⊆ P := h.prop.1

theorem IsMaxDisjointIn.disjointPred (h : IsMaxDisjointIn D P) : DisjointPred D := h.prop.2

/-- A disjoint subset is maximal when no member of the predicate can be added to it without
overlap. -/
theorem isMaxDisjointIn_iff :
    IsMaxDisjointIn D P ↔
      D ⊆ P ∧ DisjointPred D ∧ ∀ x ∈ P, x ∉ D → ¬ DisjointPred (insert x D) :=
  ⟨fun h ↦ ⟨h.subset, h.disjointPred, fun x hx hxD hd ↦
      hxD (h.2 ⟨insert_subset hx h.subset, hd⟩ (subset_insert x D) (mem_insert x D))⟩,
    fun ⟨hDP, hD, hmax⟩ ↦ ⟨⟨hDP, hD⟩, fun _ hD' hDD' x hx ↦ by_contra fun hxD ↦
      hmax x (hD'.1 hx) hxD (hD'.2.anti (insert_subset hx hDD'))⟩⟩

instance [Fintype α] [DecidableEq α] [DecidableRel (Overlap (α := α))] [DecidablePred (· ∈ D)]
    [DecidablePred (· ∈ P)] : Decidable (IsMaxDisjointIn D P) :=
  haveI (x : α) : DecidablePred (· ∈ insert x D) := fun y ↦
    decidable_of_iff (y = x ∨ y ∈ D) Iff.rfl
  decidable_of_iff ((∀ x, x ∈ D → x ∈ P) ∧ DisjointPred D ∧
    ∀ x, x ∈ P → x ∉ D → ¬ DisjointPred (insert x D)) isMaxDisjointIn_iff.symm

/-- Every member of a predicate lies in a perspective on it. -/
theorem exists_isMaxDisjointIn_mem (hx : x ∈ P) : ∃ D, IsMaxDisjointIn D P ∧ x ∈ D := by
  obtain ⟨D, hxD, hD⟩ := zorn_subset_nonempty {D | D ⊆ P ∧ DisjointPred D}
    (fun c hc hchain _ ↦ ⟨⋃₀ c, ⟨sUnion_subset fun D hD ↦ (hc hD).1,
      (pairwise_sUnion hchain.directedOn).2 fun D hD ↦ (hc hD).2⟩,
      fun D hD ↦ subset_sUnion_of_mem hD⟩)
    {x} ⟨singleton_subset_iff.2 hx, disjointPred_singleton x⟩
  exact ⟨D, hD, hxD rfl⟩

/-- The union of two distinct perspectives is not disjoint. -/
theorem IsMaxDisjointIn.not_disjointPred_union (h₁ : IsMaxDisjointIn D₁ P)
    (h₂ : IsMaxDisjointIn D₂ P) (hne : D₁ ≠ D₂) : ¬ DisjointPred (D₁ ∪ D₂) := fun h ↦
  have hP : D₁ ∪ D₂ ⊆ P ∧ DisjointPred (D₁ ∪ D₂) := ⟨union_subset h₁.subset h₂.subset, h⟩
  hne ((subset_union_left.trans (h₂.2 hP subset_union_right)).antisymm
    (subset_union_right.trans (h₁.2 hP subset_union_left)))

/-- A predicate with two distinct perspectives is not disjoint. -/
theorem IsMaxDisjointIn.not_disjointPred (h₁ : IsMaxDisjointIn D₁ P)
    (h₂ : IsMaxDisjointIn D₂ P) (hne : D₁ ≠ D₂) : ¬ DisjointPred P := fun h ↦
  h₁.not_disjointPred_union h₂ hne (h.anti (union_subset h₁.subset h₂.subset))

/-- A disjoint predicate is its own only perspective. -/
theorem DisjointPred.isMaxDisjointIn_iff_eq (h : DisjointPred P) :
    IsMaxDisjointIn D P ↔ D = P :=
  ⟨fun hD ↦ hD.subset.antisymm (hD.2 ⟨Subset.rfl, h⟩ hD.subset),
    by rintro rfl; exact ⟨⟨Subset.rfl, h⟩, fun _ hD' _ ↦ hD'.1⟩⟩

theorem DisjointPred.isMaxDisjointIn_self (h : DisjointPred P) : IsMaxDisjointIn P P :=
  h.isMaxDisjointIn_iff_eq.2 rfl

end Mereology
