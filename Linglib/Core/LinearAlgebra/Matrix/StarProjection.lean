/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The projection onto the row space of a matrix

When `A * Aᴴ` is invertible, `Aᴴ * (A * Aᴴ)⁻¹` is the Moore–Penrose pseudoinverse of `A`, and
`Aᴴ * (A * Aᴴ)⁻¹ * A` is a star projection that fixes `A` from the right. Over `ℝ` and `ℂ` it is
the orthogonal projection onto the row space of `A`.

`[UPSTREAM]` candidate.
-/

public section

namespace Matrix

variable {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [CommRing α] [StarRing α]
  {A : Matrix m n α}

theorem mul_conjTranspose_mul_inv_mul (h : IsUnit (A * Aᴴ).det) :
    A * (Aᴴ * (A * Aᴴ)⁻¹ * A) = A := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ h, Matrix.one_mul]

theorem isStarProjection_conjTranspose_mul_inv_mul (h : IsUnit (A * Aᴴ).det) :
    IsStarProjection (Aᴴ * (A * Aᴴ)⁻¹ * A) where
  isIdempotentElem := by
    rw [IsIdempotentElem, Matrix.mul_assoc _ A, mul_conjTranspose_mul_inv_mul h]
  isSelfAdjoint := by
    simp [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]

end Matrix
