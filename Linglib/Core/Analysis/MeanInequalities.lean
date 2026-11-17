/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# Gibbs' inequality for finite sums

For weights $p$ summing to $1$ and $q$ summing to at most $1$,
[Gibbs' inequality](##ENNReal.prod_rpow_le_prod_rpow_self) says
$\prod_i q_i^{p_i} \le \prod_i p_i^{p_i}$: the geometric mean of $q$ weighted by $p$ is greatest
at $q = p$. Its logarithm is the statement that the cross-entropy of $q$ relative to $p$ is at
least the entropy of $p$, which mathlib has for measures as `InformationTheory.klDiv_nonneg`. It
is the weighted inequality of arithmetic and geometric means applied to the ratios $q_i / p_i$.

With the relative frequencies of counts $x$ as the weights, it
[bounds the likelihood of the counts](##ENNReal.prod_pow_le_prod_div_sum_pow) under any $q$ by
their likelihood under their relative frequencies, so the maximum-likelihood estimate of a
categorical distribution is the empirical one.

## Implementation notes

`[UPSTREAM]` candidate for the AM-GM section of `Mathlib/Analysis/MeanInequalities.lean`. The
weights are `ℝ≥0` and the values `ℝ≥0∞`, as in `ENNReal.geom_mean_le_arith_mean_weighted`.

## TODO

* The equality case: the two geometric means agree only if `q i = p i` wherever `p i ≠ 0`, so the
  maximum-likelihood estimate is unique. It follows from
  `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`.

## References

* [cover-thomas-2006]
-/

public section

open Finset
open scoped NNReal ENNReal

namespace ENNReal

variable {ι : Type*} {s : Finset ι}

/-- **Gibbs' inequality**: the geometric mean of `q` weighted by `p`, over `q` summing to at most
`1`, is greatest at `q = p`. -/
theorem prod_rpow_le_prod_rpow_self (p : ι → ℝ≥0) (q : ι → ℝ≥0∞) (hp : ∑ i ∈ s, p i = 1)
    (hq : ∑ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, q i ^ (p i : ℝ) ≤ ∏ i ∈ s, (p i : ℝ≥0∞) ^ (p i : ℝ) := by
  have hsplit : ∀ i ∈ s, q i ^ (p i : ℝ) = (q i / p i) ^ (p i : ℝ) * (p i : ℝ≥0∞) ^ (p i : ℝ) :=
    fun i _ ↦ by
      rcases eq_or_ne (p i) 0 with h | h
      · simp [h]
      · rw [← mul_rpow_of_nonneg _ _ (p i).coe_nonneg,
          ENNReal.div_mul_cancel (coe_ne_zero.mpr h) coe_ne_top]
  rw [prod_congr rfl hsplit, prod_mul_distrib]
  exact mul_le_of_le_one_left' <| (geom_mean_le_arith_mean_weighted s p _ hp).trans <|
    (sum_le_sum fun _ _ ↦ mul_div_le).trans hq

/-- **Maximum likelihood of a categorical distribution.** Under weights `w` summing to at most
`1`, counts `x` have likelihood at most their likelihood under their relative frequencies. -/
theorem prod_pow_le_prod_div_sum_pow {w : ι → ℝ≥0∞} (hsum : ∑ i ∈ s, w i ≤ 1) (x : ι → ℕ) :
    ∏ i ∈ s, w i ^ x i ≤ ∏ i ∈ s, ((x i : ℝ≥0∞) / ∑ j ∈ s, (x j : ℝ≥0∞)) ^ x i := by
  rcases Nat.eq_zero_or_pos (∑ j ∈ s, x j) with hX | hX
  · exact le_of_eq (prod_congr rfl fun i hi ↦ by simp [sum_eq_zero_iff.mp hX i hi])
  have hX' : (∑ j ∈ s, (x j : ℝ≥0)) ≠ 0 := by exact_mod_cast hX.ne'
  have h := rpow_le_rpow (z := ((∑ j ∈ s, x j : ℕ) : ℝ))
    (prod_rpow_le_prod_rpow_self (fun i ↦ (x i : ℝ≥0) / ∑ j ∈ s, (x j : ℝ≥0)) w
      (by rw [← Finset.sum_div, _root_.div_self hX']) hsum) (Nat.cast_nonneg _)
  have hpow (a : ℝ≥0∞) (i : ι) :
      (a ^ (((x i : ℝ≥0) / ∑ j ∈ s, (x j : ℝ≥0) : ℝ≥0) : ℝ)) ^ ((∑ j ∈ s, x j : ℕ) : ℝ) =
        a ^ x i := by
    rw [← rpow_mul, ← rpow_natCast]
    congr 1
    push_cast
    exact div_mul_cancel₀ _ (by exact_mod_cast hX.ne')
  simpa only [← prod_rpow_of_nonneg (Nat.cast_nonneg _), hpow, coe_div hX', ofNNReal_finsetSum,
    coe_natCast] using h

end ENNReal
