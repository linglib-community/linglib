/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.PiLex
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Linarith

/-!
# Weighted sums and the lexicographic order

A weighted sum `v ↦ ∑ i, w i * v i` of vectors with entries at most `M` is strictly monotone for
the lexicographic order exactly when each weight exceeds `M` times the sum of the weights after
it (`Pi.strictMonoOn_sum_mul_iff`, for `M ≥ 1`). With the weights `(M + 1) ^ (n - 1 - i)` the sum
is the base-`M + 1` numeral whose digits are the vector, the canonical such weighting.

[UPSTREAM] candidate for `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`.
-/

@[expose] public section

open Finset

namespace Pi

section WeightedSum

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {n M : ℕ}
  {w : Fin n → R}

/-- Weights each exceeding `M` times the sum of the later weights are positive. -/
theorem pos_of_forall_natCast_mul_sum_Ioi_lt (hw : ∀ k, (M : R) * ∑ i ∈ Ioi k, w i < w k)
    (k : Fin n) : 0 < w k := by
  induction k using WellFoundedGT.induction with
  | _ k ih =>
    exact (mul_nonneg M.cast_nonneg (sum_nonneg fun i hi ↦ (ih i (mem_Ioi.1 hi)).le)).trans_lt
      (hw k)

/-- Weights each exceeding `M` times the sum of the later weights make the weighted sum strictly
monotone for the lexicographic order on vectors with entries at most `M`. -/
theorem strictMonoOn_sum_mul (hw : ∀ k, (M : R) * ∑ i ∈ Ioi k, w i < w k) :
    StrictMonoOn (fun v : Lex (Fin n → ℕ) ↦ ∑ i, w i * (ofLex v i : R))
      {v | ∀ i, ofLex v i ≤ M} := by
  intro a ha b hb hab
  obtain ⟨k, hk_eq, hk_lt⟩ :
      ∃ k, (∀ j < k, ofLex a j = ofLex b j) ∧ ofLex a k < ofLex b k := hab
  have hpos := pos_of_forall_natCast_mul_sum_Ioi_lt hw
  rw [← sub_pos, ← sum_sub_distrib]
  simp only [← mul_sub]
  rw [← add_sum_erase _ _ (mem_univ k), ← compl_singleton, ← Ioi_disjUnion_Iio, sum_disjUnion,
    sum_eq_zero (s := Iio k) fun j hj ↦ by rw [hk_eq j (mem_Iio.1 hj), sub_self, mul_zero],
    add_zero]
  have hk : w k ≤ w k * ((ofLex b k : R) - ofLex a k) := by
    have : (ofLex a k : R) + 1 ≤ ofLex b k := by exact_mod_cast hk_lt
    exact le_mul_of_one_le_right (hpos k).le (by linarith)
  have hrest :
      -((M : R) * ∑ i ∈ Ioi k, w i) ≤ ∑ i ∈ Ioi k, w i * ((ofLex b i : R) - ofLex a i) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun i _ ↦ ?_
    have : -(M : R) ≤ (ofLex b i : R) - ofLex a i := by
      have h₁ : (ofLex a i : R) ≤ M := by exact_mod_cast ha i
      have h₂ : (0 : R) ≤ ofLex b i := Nat.cast_nonneg _
      linarith
    nlinarith [hpos i]
  linarith [hw k]

/-- A weighted sum is strictly monotone for the lexicographic order on vectors with entries at
most `M`, for `M ≥ 1`, iff each weight exceeds `M` times the sum of the later weights. -/
theorem strictMonoOn_sum_mul_iff (hM : 0 < M) :
    StrictMonoOn (fun v : Lex (Fin n → ℕ) ↦ ∑ i, w i * (ofLex v i : R))
      {v | ∀ i, ofLex v i ≤ M} ↔ ∀ k, (M : R) * ∑ i ∈ Ioi k, w i < w k := by
  classical
  refine ⟨fun h k ↦ ?_, strictMonoOn_sum_mul⟩
  have hlt : toLex (fun i ↦ if k < i then M else 0) < toLex (Pi.single k 1 : Fin n → ℕ) :=
    ⟨k, fun j hj ↦ by simp [hj.not_gt, hj.ne], by simp⟩
  have := h (fun i ↦ by simp only [ofLex_toLex]; split_ifs <;> omega)
    (fun i ↦ by simp only [ofLex_toLex, Pi.single_apply]; split_ifs <;> omega) hlt
  rw [mul_sum]
  simpa [Pi.single_apply, sum_ite, filter_lt_eq_Ioi, mul_comm] using this

end WeightedSum

end Pi
