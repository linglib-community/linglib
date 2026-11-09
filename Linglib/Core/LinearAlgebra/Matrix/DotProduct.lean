/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Monotonicity of the dot product

`[UPSTREAM]` Mathlib proves that `w ⬝ᵥ u ≤ w ⬝ᵥ v` when `u ≤ v` pointwise and `w` is nonnegative
(`dotProduct_le_dotProduct_of_nonneg_left`). This file adds
[the strict version](##dotProduct_lt_dotProduct_of_nonneg_left): the inequality is strict as soon
as `u` lies strictly below `v` at a coordinate where `w` is positive, so a weighted sum respects a
Pareto improvement on any positively weighted coordinate. Over an ordered field the converse holds:
[`u ≤ v` iff every strictly positive weighting ranks `u` below
`v`](##le_iff_forall_pos_dotProduct_le), the self-duality of the nonnegative orthant.

## Implementation notes

`gcongr` does not prove these, since its strict-sum lemma `Finset.sum_lt_sum_of_nonempty` asks for
a strict increase at every coordinate, which fails at the coordinates `w` weights by zero.
-/

public section

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

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {u v : n → K}

theorem le_iff_forall_pos_dotProduct_le :
    u ≤ v ↔ ∀ w : n → K, (∀ i, 0 < w i) → w ⬝ᵥ u ≤ w ⬝ᵥ v := by
  refine ⟨fun h w hw ↦ dotProduct_le_dotProduct_of_nonneg_left h fun i ↦ (hw i).le, fun h ↦ ?_⟩
  by_contra huv
  obtain ⟨i, hi⟩ : ∃ i, v i < u i := by simpa [Pi.le_def] using huv
  classical
  set d := u - v
  have hd : 0 < d i := sub_pos.2 hi
  -- weight coordinate `i` heavily enough to outweigh all the others
  set M := |1 ⬝ᵥ d| / d i + 1
  have hw : ∀ j, 0 < (1 + Pi.single i M : n → K) j := fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using add_pos one_pos (by positivity : 0 < M)
    · simp [hj]
  have h' := h _ hw
  rw [← sub_nonpos, ← dotProduct_sub, add_dotProduct, single_dotProduct] at h'
  have : M * d i = |1 ⬝ᵥ d| + d i := by simp only [M, add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
  linarith [neg_abs_le (1 ⬝ᵥ d)]

theorem lt_iff_forall_pos_dotProduct_lt :
    u < v ↔ ∀ w : n → K, (∀ i, 0 < w i) → w ⬝ᵥ u < w ⬝ᵥ v := by
  refine ⟨fun h w hw ↦ ?_, fun h ↦ lt_of_le_not_ge (le_iff_forall_pos_dotProduct_le.2
    fun w hw ↦ (h w hw).le) fun hvu ↦ (h 1 fun _ ↦ one_pos).not_ge
      (le_iff_forall_pos_dotProduct_le.1 hvu 1 fun _ ↦ one_pos)⟩
  obtain ⟨i, hi⟩ := (Pi.lt_def.1 h).2
  exact dotProduct_lt_dotProduct_of_nonneg_left h.le (fun i ↦ (hw i).le) ⟨i, hw i, hi⟩

end Field
