module

public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.LatticeIntervals

/-!
# Symmetric alternatives

Two alternatives are symmetric for an assertion when they partition it: negating either one
asserts the other, so no theory that strengthens an assertion by negating alternatives can
negate one of them without the other. This is the configuration of [kroch-1972]'s symmetry
problem for scalar implicature, and [fox-katzir-2011]'s definition of it. The file defines
`IsSymmetric`, shows that the second symmetric alternative is the assertion without the first,
that symmetric alternatives are complements below the assertion (`isSymmetric_iff_isCompl`), and
that a set of propositions closed under negation and conjunction, a `BooleanSubalgebra`, contains
both or neither. The namespace `Alternatives` is the owner of terms of the theory of formal
alternatives about sets of propositions, Fox and Katzir's symmetric alternatives here.

## References

* [kroch-1972]
* [horn-1972]
* [katzir-2007]
* [fox-katzir-2011]
-/

@[expose] public section

namespace Alternatives

variable {W : Type*} {s s₁ s₂ : Set W}

/-- `s₁` and `s₂` are symmetric alternatives of `s`: they partition it. -/
structure IsSymmetric (s s₁ s₂ : Set W) : Prop where
  union : s₁ ∪ s₂ = s
  disjoint : Disjoint s₁ s₂

theorem isSymmetric_sdiff {t : Set W} (h : t ⊆ s) : IsSymmetric s t (s \ t) :=
  ⟨Set.union_sdiff_cancel h, Set.disjoint_sdiff_right⟩

theorem isSymmetric_iff_isCompl (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    IsSymmetric s s₁ s₂ ↔ IsCompl (⟨s₁, h₁⟩ : Set.Iic s) ⟨s₂, h₂⟩ := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · rintro ⟨hu, hd⟩
    exact ⟨Subtype.ext (by simpa using hd.eq_bot), Subtype.ext (by simpa using hu)⟩
  · rintro ⟨hd, hu⟩
    exact ⟨by simpa using congrArg Subtype.val hu,
      Set.disjoint_iff_inter_eq_empty.2 (by simpa using congrArg Subtype.val hd)⟩

namespace IsSymmetric

theorem symm (h : IsSymmetric s s₁ s₂) : IsSymmetric s s₂ s₁ :=
  ⟨(Set.union_comm _ _).trans h.union, h.disjoint.symm⟩

theorem subset_left (h : IsSymmetric s s₁ s₂) : s₁ ⊆ s := h.union ▸ Set.subset_union_left

theorem subset_right (h : IsSymmetric s s₁ s₂) : s₂ ⊆ s := h.union ▸ Set.subset_union_right

theorem sdiff_eq (h : IsSymmetric s s₁ s₂) : s \ s₁ = s₂ := by
  rw [← h.union, Set.union_sdiff_left]
  exact h.disjoint.symm.sdiff_eq_left

theorem not_subset_left (h : IsSymmetric s s₁ s₂) (hne : s₂.Nonempty) : ¬ s ⊆ s₁ :=
  fun hsub ↦ let ⟨_, hw⟩ := hne; Set.disjoint_left.1 h.disjoint (hsub (h.subset_right hw)) hw

theorem ssubset_left (h : IsSymmetric s s₁ s₂) (hne : s₂.Nonempty) : s₁ ⊂ s :=
  h.subset_left.ssubset_of_not_subset (h.not_subset_left hne)

theorem mem_of_mem (h : IsSymmetric s s₁ s₂) {R : BooleanSubalgebra (Set W)} (hs : s ∈ R)
    (h₁ : s₁ ∈ R) : s₂ ∈ R :=
  h.sdiff_eq ▸ BooleanSubalgebra.sdiff_mem hs h₁

end IsSymmetric

theorem isSymmetric_coe [DecidableEq W] (A B C : Finset W) :
    IsSymmetric (↑A : Set W) ↑B ↑C ↔ B ∪ C = A ∧ B ∩ C = ∅ := by
  constructor
  · rintro ⟨hu, hd⟩
    refine ⟨Finset.coe_inj.1 (by rw [Finset.coe_union, hu]), ?_⟩
    exact Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_coe.1 hd)
  · rintro ⟨hu, hd⟩
    refine ⟨by rw [← Finset.coe_union, hu], ?_⟩
    exact Finset.disjoint_coe.2 (Finset.disjoint_iff_inter_eq_empty.2 hd)

end Alternatives
