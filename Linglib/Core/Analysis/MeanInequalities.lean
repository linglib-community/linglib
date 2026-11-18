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
at $q = p$. It is the weighted inequality of arithmetic and geometric means applied to the ratios
$q_i / p_i$, which [bounds the left side by $\sum_i q_i$ times the
right](##ENNReal.prod_rpow_le_sum_mul_prod_rpow_self) with no condition on $q$. Its logarithm says
the cross-entropy of $q$ relative to $p$ is at least the entropy of $p$; mathlib has that for
measures as `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`.

With the relative frequencies of counts $x$ as the weights, it
[bounds the likelihood of the counts](##ENNReal.prod_pow_le_prod_div_sum_pow) under any $q$ by
their likelihood under their relative frequencies, so the maximum-likelihood estimate of a
categorical distribution is the empirical one. Equality holds
[only at $q = p$](##ENNReal.prod_rpow_eq_prod_rpow_self_iff), so the estimate
[is unique](##ENNReal.prod_pow_eq_prod_div_sum_pow_iff).

## Implementation notes

`[UPSTREAM]` candidate for the AM-GM section of `Mathlib/Analysis/MeanInequalities.lean`. The
Each statement comes in `Real`, `NNReal` and `ENNReal` versions with the arguments of the
corresponding `geom_mean_le_arith_mean_weighted`; the `ℝ≥0∞` equality case is transferred from the
real one.

## References

* [cover-thomas-2006]
-/

public section

open Finset
open scoped NNReal ENNReal

namespace Real

variable {ι : Type*} {s : Finset ι} {p q : ι → ℝ}

private theorem rpow_eq_div_rpow_mul_rpow_self (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∀ i ∈ s, q i ^ p i = (q i / p i) ^ p i * p i ^ p i := fun i hi ↦ by
  rcases (hp i hi).eq_or_lt with h | h
  · simp [← h]
  · rw [← mul_rpow (div_nonneg (hq i hi) h.le) h.le, div_mul_cancel₀ _ h.ne']

private theorem sum_mul_div_le (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∀ i ∈ s, p i * (q i / p i) ≤ q i := fun i hi ↦ by
  rcases (hp i hi).eq_or_lt with h | h
  · simpa [← h] using hq i hi
  · exact (mul_div_cancel₀ _ h.ne').le

variable (s p q)

/-- **Gibbs' inequality**, homogeneous in `q`: the geometric mean of `q` weighted by `p` is at
most the total of `q` times the geometric mean of `p` weighted by itself. -/
theorem prod_rpow_le_sum_mul_prod_rpow_self (hp : ∀ i ∈ s, 0 ≤ p i) (hp' : ∑ i ∈ s, p i = 1)
    (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∏ i ∈ s, q i ^ p i ≤ (∑ i ∈ s, q i) * ∏ i ∈ s, p i ^ p i := by
  rw [prod_congr rfl (rpow_eq_div_rpow_mul_rpow_self hp hq), prod_mul_distrib]
  exact mul_le_mul_of_nonneg_right
    ((geom_mean_le_arith_mean_weighted s p _ hp hp' fun i hi ↦
      div_nonneg (hq i hi) (hp i hi)).trans (sum_le_sum (sum_mul_div_le hp hq)))
    (prod_nonneg fun i hi ↦ rpow_nonneg (hp i hi) _)

/-- **Gibbs' inequality**: the geometric mean of `q` weighted by `p`, over `q` summing to at most
`1`, is greatest at `q = p`. -/
theorem prod_rpow_le_prod_rpow_self (hp : ∀ i ∈ s, 0 ≤ p i) (hp' : ∑ i ∈ s, p i = 1)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hq' : ∑ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, q i ^ p i ≤ ∏ i ∈ s, p i ^ p i :=
  (prod_rpow_le_sum_mul_prod_rpow_self s p q hp hp' hq).trans
    (mul_le_of_le_one_left (prod_nonneg fun i hi ↦ rpow_nonneg (hp i hi) _) hq')

/-- **Gibbs' inequality, equality case**: the geometric mean of `q` weighted by `p`, over `q`
summing to at most `1`, attains its greatest value only at `q = p`. -/
theorem prod_rpow_eq_prod_rpow_self_iff (hp : ∀ i ∈ s, 0 ≤ p i) (hp' : ∑ i ∈ s, p i = 1)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hq' : ∑ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, q i ^ p i = ∏ i ∈ s, p i ^ p i ↔ ∀ i ∈ s, q i = p i := by
  refine ⟨fun h ↦ ?_, fun h ↦ prod_congr rfl fun i hi ↦ by rw [h i hi]⟩
  have hz : ∀ i ∈ s, 0 ≤ q i / p i := fun i hi ↦ div_nonneg (hq i hi) (hp i hi)
  have hP : 0 < ∏ i ∈ s, p i ^ p i := prod_pos fun i hi ↦ by
    rcases (hp i hi).eq_or_lt with h | h
    · simp [← h]
    · exact rpow_pos_of_pos h _
  rw [prod_congr rfl (rpow_eq_div_rpow_mul_rpow_self hp hq), prod_mul_distrib,
    mul_eq_right₀ hP.ne'] at h
  have hle := sum_le_sum (sum_mul_div_le hp hq)
  have hA : ∑ i ∈ s, p i * (q i / p i) = 1 :=
    le_antisymm (hle.trans hq') (h ▸ geom_mean_le_arith_mean_weighted s p _ hp hp' hz)
  have hterm := (sum_eq_sum_iff_of_le (sum_mul_div_le hp hq)).mp
    (le_antisymm hle (hq'.trans_eq hA.symm))
  have hone :=
    (geom_mean_eq_arith_mean_weighted_iff_of_nonneg' s p _ hp hp' hz).mp (h.trans hA.symm)
  intro i hi
  rcases (hp i hi).eq_or_lt with h0 | h0
  · rw [← hterm i hi, ← h0, zero_mul]
  · rw [← hterm i hi, hone i hi h0.ne', hA, mul_one]

end Real

namespace NNReal

variable {ι : Type*} (s : Finset ι)

/-- **Gibbs' inequality**: the geometric mean of `q` weighted by `p`, over `q` summing to at most
`1`, is greatest at `q = p`. -/
theorem prod_rpow_le_prod_rpow_self (p q : ι → ℝ≥0) (hp : ∑ i ∈ s, p i = 1)
    (hq : ∑ i ∈ s, q i ≤ 1) : ∏ i ∈ s, q i ^ (p i : ℝ) ≤ ∏ i ∈ s, p i ^ (p i : ℝ) := by
  exact_mod_cast Real.prod_rpow_le_prod_rpow_self s (fun i ↦ (p i : ℝ)) (fun i ↦ (q i : ℝ))
    (fun i _ ↦ (p i).coe_nonneg) (by exact_mod_cast hp) (fun i _ ↦ (q i).coe_nonneg)
    (by exact_mod_cast hq)

/-- **Gibbs' inequality, equality case**: the geometric mean of `q` weighted by `p`, over `q`
summing to at most `1`, attains its greatest value only at `q = p`. -/
theorem prod_rpow_eq_prod_rpow_self_iff (p q : ι → ℝ≥0) (hp : ∑ i ∈ s, p i = 1)
    (hq : ∑ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, q i ^ (p i : ℝ) = ∏ i ∈ s, p i ^ (p i : ℝ) ↔ ∀ i ∈ s, q i = p i := by
  exact_mod_cast Real.prod_rpow_eq_prod_rpow_self_iff s (fun i ↦ (p i : ℝ)) (fun i ↦ (q i : ℝ))
    (fun i _ ↦ (p i).coe_nonneg) (by exact_mod_cast hp) (fun i _ ↦ (q i).coe_nonneg)
    (by exact_mod_cast hq)

end NNReal

namespace ENNReal

variable {ι : Type*} (s : Finset ι)

/-- **Gibbs' inequality**, homogeneous in `q`: the geometric mean of `q` weighted by `p` is at
most the total of `q` times the geometric mean of `p` weighted by itself. -/
theorem prod_rpow_le_sum_mul_prod_rpow_self (p : ι → ℝ≥0) (q : ι → ℝ≥0∞)
    (hp : ∑ i ∈ s, p i = 1) :
    ∏ i ∈ s, q i ^ (p i : ℝ) ≤ (∑ i ∈ s, q i) * ∏ i ∈ s, (p i : ℝ≥0∞) ^ (p i : ℝ) := by
  have hsplit : ∀ i ∈ s, q i ^ (p i : ℝ) = (q i / p i) ^ (p i : ℝ) * (p i : ℝ≥0∞) ^ (p i : ℝ) :=
    fun i _ ↦ by
      rcases eq_or_ne (p i) 0 with h | h
      · simp [h]
      · rw [← mul_rpow_of_nonneg _ _ (p i).coe_nonneg,
          ENNReal.div_mul_cancel (coe_ne_zero.mpr h) coe_ne_top]
  rw [prod_congr rfl hsplit, prod_mul_distrib]
  gcongr
  exact (geom_mean_le_arith_mean_weighted s p _ hp).trans (sum_le_sum fun _ _ ↦ mul_div_le)

/-- **Gibbs' inequality**: the geometric mean of `q` weighted by `p`, over `q` summing to at most
`1`, is greatest at `q = p`. -/
theorem prod_rpow_le_prod_rpow_self (p : ι → ℝ≥0) (q : ι → ℝ≥0∞) (hp : ∑ i ∈ s, p i = 1)
    (hq : ∑ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, q i ^ (p i : ℝ) ≤ ∏ i ∈ s, (p i : ℝ≥0∞) ^ (p i : ℝ) :=
  (prod_rpow_le_sum_mul_prod_rpow_self s p q hp).trans (mul_le_of_le_one_left' hq)

/-- **Gibbs' inequality, equality case**: the geometric mean of `q` weighted by `p`, over `q`
summing to at most `1`, attains its greatest value only at `q = p`. -/
theorem prod_rpow_eq_prod_rpow_self_iff (p : ι → ℝ≥0) (q : ι → ℝ≥0∞) (hp : ∑ i ∈ s, p i = 1)
    (hq : ∑ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, q i ^ (p i : ℝ) = ∏ i ∈ s, (p i : ℝ≥0∞) ^ (p i : ℝ) ↔ ∀ i ∈ s, q i = p i := by
  have hq' : ∀ i ∈ s, q i ≠ ⊤ := fun i hi ↦
    ne_top_of_le_ne_top one_ne_top ((single_le_sum (fun _ _ ↦ zero_le) hi).trans hq)
  have hsum : ∑ i ∈ s, (q i).toReal ≤ 1 := by
    rw [← toReal_sum hq']
    exact toReal_le_of_le_ofReal zero_le_one (hq.trans_eq ofReal_one.symm)
  rw [← toReal_eq_toReal_iff' (prod_ne_top fun i hi ↦ rpow_ne_top_of_nonneg (p i).coe_nonneg
      (hq' i hi)) (prod_ne_top fun i _ ↦ rpow_ne_top_of_nonneg (p i).coe_nonneg coe_ne_top),
    toReal_prod, toReal_prod]
  simp only [← toReal_rpow, coe_toReal]
  rw [Real.prod_rpow_eq_prod_rpow_self_iff s _ _ (fun i _ ↦ (p i).coe_nonneg)
    (by exact_mod_cast hp) (fun _ _ ↦ toReal_nonneg) hsum]
  exact forall₂_congr fun i hi ↦ by
    rw [← coe_toReal (r := p i), toReal_eq_toReal_iff' (hq' i hi) coe_ne_top]

variable {s}

private theorem prod_pow_eq_prod_rpow_rpow {x : ι → ℕ} (hX : ∑ j ∈ s, x j ≠ 0) (a : ι → ℝ≥0∞) :
    ∏ i ∈ s, a i ^ x i =
      (∏ i ∈ s, a i ^ (((x i : ℝ≥0) / ∑ j ∈ s, (x j : ℝ≥0) : ℝ≥0) : ℝ)) ^
        ((∑ j ∈ s, x j : ℕ) : ℝ) := by
  rw [← prod_rpow_of_nonneg (Nat.cast_nonneg _)]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [← rpow_mul, ← rpow_natCast]
  congr 1
  push_cast
  exact (div_mul_cancel₀ _ (by exact_mod_cast hX)).symm

private theorem coe_natCast_div_sum {x : ι → ℕ} (hX : ∑ j ∈ s, x j ≠ 0) (i : ι) :
    (((x i : ℝ≥0) / ∑ j ∈ s, (x j : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = x i / ∑ j ∈ s, (x j : ℝ≥0∞) := by
  rw [coe_div (by exact_mod_cast hX), ofNNReal_finsetSum]
  simp

private theorem sum_natCast_div_sum {x : ι → ℕ} (hX : ∑ j ∈ s, x j ≠ 0) :
    ∑ i ∈ s, (x i : ℝ≥0) / ∑ j ∈ s, (x j : ℝ≥0) = 1 := by
  rw [← Finset.sum_div, _root_.div_self (by exact_mod_cast hX)]

variable (s)

/-- **Maximum likelihood of a categorical distribution.** Under weights `w` summing to at most
`1`, counts `x` have likelihood at most their likelihood under their relative frequencies. -/
theorem prod_pow_le_prod_div_sum_pow {w : ι → ℝ≥0∞} (hsum : ∑ i ∈ s, w i ≤ 1) (x : ι → ℕ) :
    ∏ i ∈ s, w i ^ x i ≤ ∏ i ∈ s, ((x i : ℝ≥0∞) / ∑ j ∈ s, (x j : ℝ≥0∞)) ^ x i := by
  rcases eq_or_ne (∑ j ∈ s, x j) 0 with hX | hX
  · exact le_of_eq (prod_congr rfl fun i hi ↦ by simp [sum_eq_zero_iff.mp hX i hi])
  simp only [← coe_natCast_div_sum hX]
  rw [prod_pow_eq_prod_rpow_rpow hX, prod_pow_eq_prod_rpow_rpow hX]
  exact rpow_le_rpow (prod_rpow_le_prod_rpow_self s _ w (sum_natCast_div_sum hX) hsum)
    (Nat.cast_nonneg _)

/-- **Uniqueness of the maximum-likelihood estimate.** Under weights `w` summing to at most `1`,
counts `x` that are not all `0` attain their greatest likelihood only at their relative
frequencies. -/
theorem prod_pow_eq_prod_div_sum_pow_iff {w : ι → ℝ≥0∞} (hsum : ∑ i ∈ s, w i ≤ 1) {x : ι → ℕ}
    (hX : ∑ j ∈ s, x j ≠ 0) :
    ∏ i ∈ s, w i ^ x i = ∏ i ∈ s, ((x i : ℝ≥0∞) / ∑ j ∈ s, (x j : ℝ≥0∞)) ^ x i ↔
      ∀ i ∈ s, w i = x i / ∑ j ∈ s, (x j : ℝ≥0∞) := by
  simp only [← coe_natCast_div_sum hX]
  rw [prod_pow_eq_prod_rpow_rpow hX, prod_pow_eq_prod_rpow_rpow hX,
    (rpow_left_injective (by exact_mod_cast hX)).eq_iff,
    prod_rpow_eq_prod_rpow_self_iff s _ w (sum_natCast_div_sum hX) hsum]

end ENNReal
