/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# The likelihood of counts under a categorical distribution

Draws with counts `x` have probability `∏ i, w i ^ x i` under the categorical distribution `w`,
and among all `w` on the simplex this is greatest at the relative frequencies `x i / ∑ x`: the
maximum-likelihood estimate of a categorical distribution is the empirical one. The bound holds
for every `w` with `∑ w ≤ 1`, and follows from the weighted inequality of arithmetic and geometric
means with the counts as weights.

## Main results

* `Real.prod_pow_le_prod_div_sum_pow`, `ENNReal.prod_pow_le_prod_div_sum_pow`: the likelihood of
  counts is at most their likelihood under their relative frequencies.
-/

@[expose] public section

open Finset

variable {ι : Type*} {s : Finset ι}

/-- **Maximum likelihood of a categorical distribution.** Under weights `w` summing to at most
`1`, counts `x` have likelihood at most their likelihood under their relative frequencies. -/
theorem Real.prod_pow_le_prod_div_sum_pow {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i ≤ 1) (x : ι → ℕ) :
    ∏ i ∈ s, w i ^ x i ≤ ∏ i ∈ s, ((x i : ℝ) / ∑ j ∈ s, (x j : ℝ)) ^ x i := by
  set X : ℝ := ∑ j ∈ s, (x j : ℝ)
  rcases (sum_nonneg fun j _ ↦ Nat.cast_nonneg (x j) : 0 ≤ X).eq_or_lt with hX | hX
  · have h0 : ∀ i ∈ s, x i = 0 := fun i hi ↦ by
      exact_mod_cast (sum_eq_zero_iff_of_nonneg fun j _ ↦ Nat.cast_nonneg (x j)).mp hX.symm i hi
    exact le_of_eq (prod_congr rfl fun i hi ↦ by simp [h0 i hi])
  -- `z i * (x i / X) = w i` wherever `x i ≠ 0`, and the `z i` have weighted mean at most `1`.
  set z : ι → ℝ := fun i ↦ w i * X / x i
  have hz : ∀ i ∈ s, 0 ≤ z i := fun i hi ↦
    div_nonneg (mul_nonneg (hw i hi) hX.le) (Nat.cast_nonneg _)
  have hxz : ∑ i ∈ s, (x i : ℝ) * z i ≤ X :=
    calc ∑ i ∈ s, (x i : ℝ) * z i ≤ ∑ i ∈ s, w i * X := sum_le_sum fun i hi ↦ by
          rcases (Nat.cast_nonneg (x i) : (0 : ℝ) ≤ x i).eq_or_lt with h | h
          · rw [← h, zero_mul]; exact mul_nonneg (hw i hi) hX.le
          · exact (mul_div_cancel₀ _ h.ne').le
      _ = (∑ i ∈ s, w i) * X := (sum_mul ..).symm
      _ ≤ X := mul_le_of_le_one_left hX.le hsum
  have hz1 : ∏ i ∈ s, z i ^ x i ≤ 1 := by
    have h := (Real.geom_mean_le_arith_mean s (fun i ↦ (x i : ℝ)) z
      (fun i _ ↦ Nat.cast_nonneg _) hX hz).trans ((div_le_one hX).mpr hxz)
    simp only [Real.rpow_natCast] at h
    exact le_of_not_gt fun h' ↦ (Real.one_lt_rpow h' (inv_pos.mpr hX)).not_ge h
  have hsplit : ∀ i ∈ s, w i ^ x i = z i ^ x i * ((x i : ℝ) / X) ^ x i := fun i _ ↦ by
    rcases Nat.eq_zero_or_pos (x i) with h | h
    · simp [h]
    · rw [← mul_pow, div_mul_div_cancel₀ (by positivity : (x i : ℝ) ≠ 0),
        mul_div_cancel_right₀ _ (hX.ne' : X ≠ 0)]
  rw [prod_congr rfl hsplit, prod_mul_distrib]
  exact mul_le_of_le_one_left (prod_nonneg fun i _ ↦ by positivity) hz1

/-- **Maximum likelihood of a categorical distribution.** Under weights `w` summing to at most
`1`, counts `x` have likelihood at most their likelihood under their relative frequencies. -/
theorem ENNReal.prod_pow_le_prod_div_sum_pow {w : ι → ENNReal} (hsum : ∑ i ∈ s, w i ≤ 1)
    (x : ι → ℕ) :
    ∏ i ∈ s, w i ^ x i ≤ ∏ i ∈ s, ((x i : ENNReal) / ∑ j ∈ s, (x j : ENNReal)) ^ x i := by
  have hw : ∀ i ∈ s, w i ≠ ⊤ := fun i hi ↦
    ne_top_of_le_ne_top one_ne_top ((single_le_sum (fun _ _ ↦ zero_le) hi).trans hsum)
  have hsum' : ∑ i ∈ s, (w i).toReal ≤ 1 := by
    rw [← ENNReal.toReal_sum hw]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (hsum.trans_eq ENNReal.ofReal_one.symm)
  have hL : ∏ i ∈ s, w i ^ x i = .ofReal (∏ i ∈ s, (w i).toReal ^ x i) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ ↦ by positivity]
    exact prod_congr rfl fun i hi ↦ by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hw i hi)]
  have hR : ∏ i ∈ s, ((x i : ENNReal) / ∑ j ∈ s, (x j : ENNReal)) ^ x i =
      .ofReal (∏ i ∈ s, ((x i : ℝ) / ∑ j ∈ s, (x j : ℝ)) ^ x i) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ ↦
      pow_nonneg (div_nonneg (Nat.cast_nonneg _) (sum_nonneg fun j _ ↦ Nat.cast_nonneg _)) _]
    refine prod_congr rfl fun i hi ↦ ?_
    rcases Nat.eq_zero_or_pos (x i) with h | h
    · simp [h]
    have hpos : (0 : ℝ) < ∑ j ∈ s, (x j : ℝ) :=
      (Nat.cast_pos.mpr h).trans_le (single_le_sum (fun j _ ↦ Nat.cast_nonneg (x j)) hi)
    rw [ENNReal.ofReal_pow (div_nonneg (Nat.cast_nonneg _) hpos.le),
      ENNReal.ofReal_div_of_pos hpos, ← Nat.cast_sum,
      ← Nat.cast_sum, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal (Real.prod_pow_le_prod_div_sum_pow
    (fun i _ ↦ ENNReal.toReal_nonneg) hsum' x)
