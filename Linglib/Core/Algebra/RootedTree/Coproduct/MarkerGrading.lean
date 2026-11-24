/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Marker
public import Linglib.Core.Combinatorics.RootedTree.MarkerCutConservation

/-!
# The edge grading of the marker coproduct

The algebra `ConnesKreimer R (UnorderedTree (α ⊕ β))` is graded by the number of edges of a forest.
A marker cut conserves edges, so the marker coproduct takes a forest with `n` edges into the sum of
the tensor products of the pieces of degrees `i` and `j` with `i + j = n`.

## Main definitions

* `ConnesKreimer.gradedPiece`: the span of the forests with `n` edges.

## Main results

* `ConnesKreimer.markerComulAlgHom_of'_mem_gradedSpan`: the marker coproduct preserves the grading.

## TODO

Once mathlib's graded coalgebra and bialgebra API lands (leanprover-community/mathlib4#39849),
restate `gradedPiece` as a `DirectSum.Decomposition` and this file's content as a `GradedBialgebra`
instance.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommRing R] {α β : Type*}

/-! ### Edge-count grading -/

/-- The graded piece `V_n` is the subspace of `ConnesKreimer R (UnorderedTree X)`
    spanned by forests with exactly `n` edges. -/
noncomputable def gradedPiece (X : Type*) (n : ℕ) :
    Submodule R (ConnesKreimer R (UnorderedTree X)) :=
  Submodule.span R
    {x | ∃ F : Forest (UnorderedTree X),
      (F.map UnorderedTree.numEdges).sum = n ∧ x = ConnesKreimer.of' F}

/-! ### Homogeneous tensor span at fixed total edge degree -/

/-- The span of basis tensors `of' F₁ ⊗ of' F₂` with total edge count
    `n` — the homogeneous degree-`n` piece of the tensor square through
    which the marker coproduct factors. -/
private noncomputable def gradedTensorSpan (n : ℕ) :
    Submodule R (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
      ConnesKreimer R (UnorderedTree (α ⊕ β))) :=
  Submodule.span R {y | ∃ F₁ F₂ : Forest (UnorderedTree (α ⊕ β)),
    (F₁.map UnorderedTree.numEdges).sum + (F₂.map UnorderedTree.numEdges).sum = n ∧
    y = ConnesKreimer.of' F₁ ⊗ₜ[R] ConnesKreimer.of' F₂}

/-- The graded tensor spans are multiplicative, with degrees adding. -/
private theorem gradedTensorSpan_mul {m k : ℕ}
    {u v : ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
      ConnesKreimer R (UnorderedTree (α ⊕ β))}
    (hu : u ∈ gradedTensorSpan (R := R) (α := α) (β := β) m)
    (hv : v ∈ gradedTensorSpan (R := R) (α := α) (β := β) k) :
    u * v ∈ gradedTensorSpan (R := R) (α := α) (β := β) (m + k) := by
  have hle : gradedTensorSpan (R := R) (α := α) (β := β) m *
      gradedTensorSpan (R := R) (α := α) (β := β) k ≤
      gradedTensorSpan (R := R) (α := α) (β := β) (m + k) := by
    rw [gradedTensorSpan, gradedTensorSpan, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨a, ⟨F₁, F₂, hab, rfl⟩, b, ⟨G₁, G₂, hgk, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨F₁ + G₁, F₂ + G₂, ?_, ?_⟩
    · rw [Multiset.map_add, Multiset.sum_add, Multiset.map_add, Multiset.sum_add]
      omega
    · show (ConnesKreimer.of' F₁ ⊗ₜ[R] ConnesKreimer.of' F₂) *
        (ConnesKreimer.of' G₁ ⊗ₜ[R] ConnesKreimer.of' G₂) =
        ConnesKreimer.of' (F₁ + G₁) ⊗ₜ[R] ConnesKreimer.of' (F₂ + G₂)
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← ConnesKreimer.of'_add,
        ← ConnesKreimer.of'_add]
  exact hle (Submodule.mul_mem_mul hu hv)

/-- Tree-level membership: the marker coproduct of a single tree is homogeneous of
    degree the tree's edge count. -/
private theorem comulTree_mem (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    comulTreeOfCuts (R := R) (markerCuts τ) T ∈
      gradedTensorSpan (R := R) (α := α) (β := β) T.numEdges := by
  unfold comulTreeOfCuts
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.subset_span ⟨{T}, 0, ?_, ?_⟩
    · rw [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero, Multiset.sum_zero,
        add_zero]
    · rw [ConnesKreimer.of'_zero]
      rfl
  · refine multiset_sum_mem _ ?_
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hc
    refine Submodule.subset_span ⟨p.1, {p.2}, ?_, rfl⟩
    rw [Multiset.map_singleton, Multiset.sum_singleton]
    exact markerCuts_numEdges τ T p hp

/-- Forest-level membership: the marker coproduct of a forest is homogeneous of degree
    its edge count. -/
private theorem comulForest_mem (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (UnorderedTree (α ⊕ β))) :
    comulForestOfCuts (R := R) (markerCuts τ) F ∈
      gradedTensorSpan (R := R) (α := α) (β := β) ((F.map UnorderedTree.numEdges).sum) := by
  induction F using Multiset.induction_on with
  | empty =>
    rw [comulForestOfCuts_zero]
    refine Submodule.subset_span ⟨0, 0, rfl, ?_⟩
    rw [Algebra.TensorProduct.one_def, ConnesKreimer.of'_zero]
  | cons T F ih =>
    rw [show comulForestOfCuts (R := R) (markerCuts τ) (T ::ₘ F) =
          comulTreeOfCuts (R := R) (markerCuts τ) T *
            comulForestOfCuts (R := R) (markerCuts τ) F from
        comulForestOfCuts_cons _ T F,
        Multiset.map_cons, Multiset.sum_cons]
    exact gradedTensorSpan_mul (comulTree_mem τ T) ih

/-- The marker coproduct preserves the edge-count grading. -/
theorem markerComulAlgHom_of'_mem_gradedSpan
    (τ : UnorderedTree (α ⊕ β) → β) (F : Forest (UnorderedTree (α ⊕ β))) :
    markerComulAlgHom (R := R) τ (ConnesKreimer.of' F) ∈
      Submodule.span R {y | ∃ (i j : ℕ) (_hi : i + j = (F.map UnorderedTree.numEdges).sum)
        (xi yi : ConnesKreimer R (UnorderedTree (α ⊕ β))),
        xi ∈ gradedPiece (α ⊕ β) i ∧
        yi ∈ gradedPiece (α ⊕ β) j ∧
        y = xi ⊗ₜ[R] yi} := by
  -- Each cut splits the edges (the marker marker replaces the cut
  -- subtree by a unit-weight leaf, `markerCuts_numEdges`), and the
  -- homogeneous tensor spans multiply additively (`gradedTensorSpan_mul`).
  rw [markerComulAlgHom_apply_of']
  refine IsConcreteLE.le_iff.mp (Submodule.span_le.mpr ?_)
    (comulForest_mem (R := R) τ F)
  rintro y ⟨F₁, F₂, hsum, rfl⟩
  exact Submodule.subset_span
    ⟨(F₁.map UnorderedTree.numEdges).sum, (F₂.map UnorderedTree.numEdges).sum, hsum,
      ConnesKreimer.of' F₁, ConnesKreimer.of' F₂,
      Submodule.subset_span ⟨F₁, rfl, rfl⟩,
      Submodule.subset_span ⟨F₂, rfl, rfl⟩, rfl⟩

end ConnesKreimer
