module

public import Linglib.Core.Order.Concept

/-!
# Compatibility frames

This file defines compatibility frames, the possibility semantics for orthologic on which
Holliday and Mandelkern build their account of epistemic modals. A frame is a set of partial
*possibilities* with a reflexive, symmetric compatibility relation, and its propositions are the
concepts of orthogonality, the complement of compatibility. They form an ortholattice $O(F)$ in
which [$\neg A$ holds where no $A$-possibility is compatible](##mem_upperPolar_ortho),
[the propositions are the paper's regular sets](##isExtent_ortho_iff), and [a possibility can
settle a disjunction without settling either disjunct](##mem_extentClosure_ortho). The
proposition that $x$ obtains is the least one containing $x$, whose members are
[the possibilities refining $x$](##mem_ofObject_ortho), and $O(F)$ is [Boolean exactly when
compatible possibilities have a common refinement](##inf_sup_le_iff).

## Main definitions

* `Orthologic.Compatibility`: a reflexive, symmetric compatibility relation on possibilities.
* `Orthologic.Compatibility.Regular`: the ortholattice $O(F)$ of regular propositions.

## Implementation notes

A frame stores its orthogonality relation `ortho`, which defaults to `¬ compat`, in the way
`Preorder` stores `<`, so a frame built from an orthogonality relation, such as the canonical
frame of an ortholattice, keeps that relation definitionally. Everything else is mathlib's
concept API for `ortho`: negation is `upperPolar`, the regular sets are the extents, the paper's
closure operator $c_◇$ is `extentClosure`, and the set $↓x$ of refinements of $x$ is the object
concept `Concept.ofObject`, so that $y ⊑ x$ is $y ∈ ↓x$. The paper's formulas are
characterizations of these objects. Decidability of `compat` is not bundled: use sites take
`[DecidableRel F.compat]`, as for `SimpleGraph.Adj`. The paper's frames are nonempty; no result
here needs it, so the structure does not require it.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

open Order Concept

variable {S : Type*}

/-- A compatibility frame is a set of possibilities with a reflexive, symmetric compatibility
relation; two possibilities are compatible when neither settles as true anything the other
settles as false ([holliday-mandelkern-2024] Definition 4.1). -/
structure Compatibility (S : Type*) where
  /-- Compatibility of possibilities. -/
  compat : S → S → Prop
  compat_refl : Std.Refl compat
  compat_symm : Std.Symm compat
  /-- Orthogonality, the complement of compatibility. -/
  ortho : S → S → Prop := fun x y ↦ ¬ compat x y
  ortho_iff : ∀ x y, ortho x y ↔ ¬ compat x y := by intros; exact Iff.rfl

namespace Compatibility

variable (F : Compatibility S)

/-- Compatibility is reflexive. -/
theorem refl (x : S) : F.compat x x := F.compat_refl.refl x

variable {F} in
/-- Compatibility is symmetric, as `SimpleGraph.Adj.symm` is for adjacency. -/
theorem compat.symm {x y : S} (h : F.compat x y) : F.compat y x :=
  F.compat_symm.symm x y h

instance : Std.Symm F.ortho :=
  ⟨fun x y h ↦ (F.ortho_iff y x).mpr fun hc ↦ (F.ortho_iff x y).mp h hc.symm⟩

instance : Std.Irrefl F.ortho :=
  ⟨fun x h ↦ (F.ortho_iff x x).mp h (F.refl x)⟩

instance [DecidableRel F.compat] : DecidableRel F.ortho :=
  fun x y ↦ decidable_of_iff _ (F.ortho_iff x y).symm

/-- The regular propositions of `F`, its ortholattice $O(F)$, are the concepts of
orthogonality. -/
abbrev Regular : Type _ := Concept S S F.ortho

/-- The orthocomplement `¬A` holds at the possibilities compatible with no `A`-possibility,
those whose information settles `¬A` ([holliday-mandelkern-2024] Proposition 4.8, eq. (1)). -/
theorem mem_upperPolar_ortho {A : Set S} {x : S} :
    x ∈ upperPolar F.ortho A ↔ ∀ y, F.compat x y → y ∉ A :=
  ⟨fun hx y hxy hy ↦ (F.ortho_iff y x).1 (hx hy) hxy.symm,
    fun hx a ha ↦ (F.ortho_iff a x).2 fun hc ↦ hx a hc.symm ha⟩

/-- A set is regular, a concept extent of orthogonality, when every possibility outside it is
compatible with one all of whose compatible possibilities lie outside it
([holliday-mandelkern-2024] Definition 4.3). -/
theorem isExtent_ortho_iff (A : Set S) :
    IsExtent F.ortho A ↔ ∀ x, x ∈ A ∨ ∃ y, F.compat x y ∧ ∀ z, F.compat y z → z ∉ A := by
  rw [isExtent_iff_lowerPolar_upperPolar_subset, ← upperPolar_eq_lowerPolar]
  simp only [Set.subset_def, F.mem_upperPolar_ortho, or_iff_not_imp_right, not_exists, not_and,
    not_forall, not_not, exists_prop]

/-- The closure operator `c_◇` sends `A` to the possibilities all of whose compatible
possibilities are compatible with an `A`-possibility, and its fixed points are the regular sets
([holliday-mandelkern-2024] footnote 19). At `A ∪ B` it is the disjunction `A ∨ B`, so a
possibility can settle `A ∨ B` without settling either ([holliday-mandelkern-2024] eq. (2)). -/
theorem mem_extentClosure_ortho {A : Set S} {x : S} :
    x ∈ extentClosure F.ortho A ↔ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A := by
  rw [extentClosure_apply, ← upperPolar_eq_lowerPolar]
  simp only [F.mem_upperPolar_ortho, not_forall, not_not, exists_prop]

/-- A possibility `y` refines `x`, lying in the least proposition `↓x` containing `x`, iff every
possibility compatible with `y` is compatible with `x` ([holliday-mandelkern-2024] Lemmas 4.4
and 4.5). -/
theorem mem_ofObject_ortho {y x : S} :
    y ∈ ofObject F.ortho x ↔ ∀ z, F.compat y z → F.compat x z := by
  rw [mem_ofObject_iff]
  exact forall_congr' fun z ↦ by rw [F.ortho_iff, F.ortho_iff, not_imp_not]

/-- When compatibility is identity, as between the possible worlds of classical semantics,
orthocomplement is Boolean complement ([holliday-mandelkern-2024] pp. 858 and 861). -/
theorem upperPolar_ortho_eq_compl (h : ∀ x y, F.compat x y → x = y) (A : Set S) :
    upperPolar F.ortho A = Aᶜ :=
  Set.ext fun x ↦ F.mem_upperPolar_ortho.trans
    ⟨fun hx hA ↦ hx x (F.refl x) hA, fun hx y hxy ↦ h x y hxy ▸ hx⟩

/-- The regular propositions form a Boolean algebra, by distributivity, exactly when
compatibility implies compossibility: any two compatible possibilities have a common refinement
([holliday-mandelkern-2024] Remark 4.9). -/
theorem inf_sup_le_iff :
    (∀ A B C : F.Regular, A ⊓ (B ⊔ C) ≤ A ⊓ B ⊔ A ⊓ C) ↔
      ∀ x y, F.compat x y → ∃ z, z ∈ ofObject F.ortho x ∧ z ∈ ofObject F.ortho y := by
  rw [IsOrtholattice.inf_sup_le_iff_le_compl_of_disjoint]
  refine ⟨fun h x y hxy ↦ by_contra fun hne ↦ ?_, fun h A B hAB ↦ ?_⟩
  · have hd : Disjoint (ofObject F.ortho x) (ofObject F.ortho y) := disjoint_iff.2 <|
      coe_eq_empty.1 <| Set.eq_empty_of_forall_notMem fun z hz ↦ hne ⟨z, hz⟩
    exact (F.ortho_iff x y).1
      (mem_compl_ofObject_iff.1 (extent_subset_extent_iff.2 (h _ _ hd) (mem_ofObject_self y))) hxy
  refine extent_subset_extent_iff.1 fun y hy ↦ ?_
  change y ∈ ((Aᶜ : F.Regular) : Set S)
  rw [coe_compl, F.mem_upperPolar_ortho]
  intro z hyz hzA
  obtain ⟨w, hwy, hwz⟩ := h y z hyz
  have hw : w ∈ ((A ⊓ B : F.Regular) : Set S) :=
    ⟨A.isExtent_extent.mem_of_mem_ofObject hwz hzA, B.isExtent_extent.mem_of_mem_ofObject hwy hy⟩
  rwa [disjoint_iff.1 hAB, coe_bot] at hw

end Compatibility

end Orthologic
