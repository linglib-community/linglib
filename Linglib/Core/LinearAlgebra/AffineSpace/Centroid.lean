module

public import Mathlib.LinearAlgebra.AffineSpace.Centroid
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Centroids under affine and linear maps

`[UPSTREAM]` Affine maps commute with the centroids of nonempty finite families of points, the
centroid case of `Finset.map_affineCombination`; so do linear maps, a module being an affine space
over itself, and right multiplication by a matrix.

## Main results

* `Finset.map_centroid_of_nonempty`: affine maps commute with centroids of nonempty sets.
* `LinearMap.map_centroid`: so do linear maps.
* `Matrix.centroid_vecMul`: so does right multiplication by a matrix.

## Implementation notes

`Matrix.centroid_vecMul` is `LinearMap.map_centroid` for `Matrix.vecMulLinear`, stated over an
abstract index type: at a concrete `Fin n`, unifying `x ᵥ* M` with `M.vecMulLinear x` unfolds the
sums of `vecMul` and exhausts the recursion limit.
-/

@[expose] public section

open Affine

namespace Finset

variable {k V P V₂ P₂ ι : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
  [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (s : Finset ι)

/-- Affine maps commute with centroids, if the number of points, converted to `k`, is not zero. -/
theorem map_centroid_of_cast_card_ne_zero (p : ι → P) (f : P →ᵃ[k] P₂) (h : (#s : k) ≠ 0) :
    f (s.centroid k p) = s.centroid k (f ∘ p) := by
  rw [centroid_def, centroid_def,
    s.map_affineCombination p _ (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h)]

/-- In the characteristic zero case, affine maps commute with centroids of nonempty sets. -/
theorem map_centroid_of_nonempty [CharZero k] (p : ι → P) (f : P →ᵃ[k] P₂) (h : s.Nonempty) :
    f (s.centroid k p) = s.centroid k (f ∘ p) :=
  s.map_centroid_of_cast_card_ne_zero p f (Nat.cast_ne_zero.2 (card_pos.2 h).ne')

end Finset

/-- In the characteristic zero case, linear maps commute with centroids of nonempty sets. -/
theorem LinearMap.map_centroid {k V V₂ ι : Type*} [DivisionRing k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddCommGroup V₂] [Module k V₂] (f : V →ₗ[k] V₂) {s : Finset ι} (h : s.Nonempty)
    (p : ι → V) : f (s.centroid k p) = s.centroid k (f ∘ p) :=
  s.map_centroid_of_nonempty p f.toAffineMap h

open Matrix in
/-- In the characteristic zero case, right multiplication by a matrix commutes with centroids of
nonempty sets. -/
theorem Matrix.centroid_vecMul {k m n ι : Type*} [Field k] [CharZero k] [Fintype m]
    {s : Finset ι} (h : s.Nonempty) (p : ι → m → k) (M : Matrix m n k) :
    s.centroid k p ᵥ* M = s.centroid k fun i ↦ p i ᵥ* M :=
  M.vecMulLinear.map_centroid h p
