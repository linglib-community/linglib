/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Strict monotonicity of the dot product

Mathlib proves that `w ⬝ᵥ u ≤ w ⬝ᵥ v` when `u ≤ v` pointwise and `w` is nonnegative
(`dotProduct_le_dotProduct_of_nonneg_left`). This file adds the strict version, in which the
inequality is strict as soon as `u` lies strictly below `v` at a coordinate where `w` is positive.
A weighted sum therefore respects a Pareto improvement on any positively weighted coordinate.

## Main results

* `dotProduct_lt_dotProduct_of_nonneg_left`, `dotProduct_lt_dotProduct_of_nonneg_right`: the
  strict monotonicity of the dot product in either argument.
-/

@[expose] public section

variable {n R : Type*} [Fintype n] [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  {u v w : n → R}

/-- The dot product with a nonnegative vector `w` is strictly monotone in the other argument
when the increase is strict at a coordinate where `w` is positive. -/
lemma dotProduct_lt_dotProduct_of_nonneg_left (huv : u ≤ v) (hw : 0 ≤ w)
    (h : ∃ i, 0 < w i ∧ u i < v i) : w ⬝ᵥ u < w ⬝ᵥ v := by
  obtain ⟨i, hwi, hi⟩ := h
  exact Finset.sum_lt_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (huv j) (hw j))
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi hwi⟩

/-- The dot product with a nonnegative vector `w` on the right is strictly monotone in the left
argument when the increase is strict at a coordinate where `w` is positive. -/
lemma dotProduct_lt_dotProduct_of_nonneg_right (huv : u ≤ v) (hw : 0 ≤ w)
    (h : ∃ i, 0 < w i ∧ u i < v i) : u ⬝ᵥ w < v ⬝ᵥ w := by
  obtain ⟨i, hwi, hi⟩ := h
  exact Finset.sum_lt_sum (fun j _ ↦ mul_le_mul_of_nonneg_right (huv j) (hw j))
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_right hi hwi⟩
