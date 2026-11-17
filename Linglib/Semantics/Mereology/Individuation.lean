module

public import Mathlib.Order.Zorn
public import Linglib.Semantics.Mereology.Basic

/-!
# Individuation perspectives

A predicate is overlapping if two distinct members overlap, and disjoint otherwise. A maximally
disjoint subset of a predicate is an individuation perspective on it, a way of counting its
members, and [every member lies in one](##Mereology.nullSchema_eq), so the null schema, the
union of all perspectives, is the predicate itself.

## References

* [landman-2011], [landman-2020], [sutton-filip-2021]
-/

@[expose] public section

namespace Mereology

variable {α β : Type*}

/-! ### Individuation perspectives

A predicate is overlapping if two distinct members share a part, and disjoint otherwise; a
maximally disjoint subset is an individuation perspective ([landman-2011], [landman-2020]),
and the null schema of [sutton-filip-2021] unions all perspectives. The overlap relation
`ov` is a parameter (mereologically, `Overlap`). -/

section Individuation

variable (ov : α → α → Prop)

/-- A predicate overlaps if two distinct members share a part. -/
def OverlapPred (P : Set α) : Prop := ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ov x y

/-- A predicate is disjoint if no two distinct members share a part. -/
def DisjointPred (P : Set α) : Prop := ¬ OverlapPred ov P

theorem disjointPred_iff_pairwise {P : Set α} : DisjointPred ov P ↔ P.Pairwise (¬ ov · ·) := by
  simp [DisjointPred, OverlapPred, Set.Pairwise]

theorem overlapPred_mono {P Q : Set α} (h : P ⊆ Q) (hP : OverlapPred ov P) : OverlapPred ov Q :=
  let ⟨x, hx, y, hy, hne, hov⟩ := hP; ⟨x, h hx, y, h hy, hne, hov⟩

theorem DisjointPred.anti {P Q : Set α} (h : P ⊆ Q) (hQ : DisjointPred ov Q) :
    DisjointPred ov P :=
  fun hP ↦ hQ (overlapPred_mono ov h hP)

/-- `D` is a maximally disjoint subset of `P` if it is disjoint and cannot be extended within `P`
without overlap. -/
def IsMaxDisjointIn (D P : Set α) : Prop :=
  D ⊆ P ∧ DisjointPred ov D ∧ ∀ x ∈ P, x ∉ D → OverlapPred ov (insert x D)

theorem isMaxDisjointIn_iff_maximal (D P : Set α) :
    IsMaxDisjointIn ov D P ↔ Maximal (fun D ↦ D ⊆ P ∧ DisjointPred ov D) D := by
  constructor
  · rintro ⟨hDP, hD, hmax⟩
    refine ⟨⟨hDP, hD⟩, fun D' ⟨hD'P, hD'⟩ hDD' x hx ↦ ?_⟩
    by_contra hxD
    exact hD' (overlapPred_mono ov (Set.insert_subset hx hDD') (hmax x (hD'P hx) hxD))
  · rintro ⟨⟨hDP, hD⟩, hmax⟩
    refine ⟨hDP, hD, fun x hxP hxD ↦ ?_⟩
    by_contra hno
    exact hxD (hmax ⟨Set.insert_subset hxP hDP, hno⟩ (Set.subset_insert x D) (Set.mem_insert x D))

/-- The null individuation schema of `P` is the union of its maximally disjoint subsets. -/
def nullSchema (P : Set α) : Set α := {x | ∃ D, IsMaxDisjointIn ov D P ∧ x ∈ D}

theorem overlapPred_union_of_maxDisjoint_ne {D₁ D₂ P : Set α} (h₁ : IsMaxDisjointIn ov D₁ P)
    (h₂ : IsMaxDisjointIn ov D₂ P) (hne : D₁ ≠ D₂) : OverlapPred ov (D₁ ∪ D₂) := by
  obtain ⟨x, hx₂, hx₁⟩ | ⟨x, hx₁, hx₂⟩ :
      (∃ x, x ∈ D₂ ∧ x ∉ D₁) ∨ (∃ x, x ∈ D₁ ∧ x ∉ D₂) := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hcon.2 hcon.1)
  · exact overlapPred_mono ov
      (Set.insert_subset_iff.mpr ⟨Or.inr hx₂, fun a ha ↦ Or.inl ha⟩)
      (h₁.2.2 x (h₂.1 hx₂) hx₁)
  · exact overlapPred_mono ov
      (Set.insert_subset_iff.mpr ⟨Or.inl hx₁, fun a ha ↦ Or.inr ha⟩)
      (h₂.2.2 x (h₁.1 hx₁) hx₂)

theorem overlapPred_nullSchema {D₁ D₂ P : Set α} (h₁ : IsMaxDisjointIn ov D₁ P)
    (h₂ : IsMaxDisjointIn ov D₂ P) (hne : D₁ ≠ D₂) : OverlapPred ov (nullSchema ov P) :=
  overlapPred_mono ov
    (Set.union_subset (fun _ ha ↦ ⟨D₁, h₁, ha⟩) (fun _ ha ↦ ⟨D₂, h₂, ha⟩))
    (overlapPred_union_of_maxDisjoint_ne ov h₁ h₂ hne)

theorem isMaxDisjointIn_self {P : Set α} (h : DisjointPred ov P) : IsMaxDisjointIn ov P P :=
  ⟨Set.Subset.rfl, h, fun _ hy hny ↦ absurd hy hny⟩

theorem exists_isMaxDisjointIn_mem {P : Set α} {x : α} (hx : x ∈ P) :
    ∃ D, IsMaxDisjointIn ov D P ∧ x ∈ D := by
  obtain ⟨D, hxD, hD⟩ := zorn_subset_nonempty {D | D ⊆ P ∧ DisjointPred ov D}
    (fun c hc hchain _ ↦ ⟨⋃₀ c, ⟨Set.sUnion_subset fun D hD ↦ (hc hD).1,
      fun ⟨a, ⟨A, hA, haA⟩, b, ⟨B, hB, hbB⟩, hab, hov⟩ ↦
        (hchain.total hA hB).elim (fun hAB ↦ (hc hB).2 ⟨a, hAB haA, b, hbB, hab, hov⟩)
          (fun hBA ↦ (hc hA).2 ⟨a, haA, b, hBA hbB, hab, hov⟩)⟩,
      fun D hD ↦ Set.subset_sUnion_of_mem hD⟩)
    {x} ⟨Set.singleton_subset_iff.2 hx, fun ⟨a, ha, b, hb, hab, _⟩ ↦
      hab ((Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm)⟩
  refine ⟨D, ⟨hD.prop.1, hD.prop.2, fun y hy hyD ↦ ?_⟩, hxD rfl⟩
  by_contra hno
  exact hyD (hD.2 ⟨Set.insert_subset hy hD.prop.1, hno⟩ (Set.subset_insert _ _)
    (Set.mem_insert _ _))

/-- The null schema is the identity, since every member of a predicate is in some
perspective. -/
theorem nullSchema_eq (P : Set α) : nullSchema ov P = P :=
  Set.Subset.antisymm (fun _ ⟨_, hD, hx⟩ ↦ hD.1 hx)
    (fun _ hx ↦ let ⟨D, hD, hxD⟩ := exists_isMaxDisjointIn_mem ov hx; ⟨D, hD, hxD⟩)

end Individuation

theorem disjointPred_overlap_iff [PartialOrder α] [OrderBot α] {P : Set α} :
    DisjointPred Overlap P ↔ P.PairwiseDisjoint id := by
  simp only [disjointPred_iff_pairwise, overlap_iff_not_disjoint, not_not]
  rfl

end Mereology
