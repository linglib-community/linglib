/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.MeanInequalities
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Probability vectors with weights in `ℝ≥0∞`

A point of `StdSimplex ℝ≥0∞ ι` on a finite type is a probability vector, the masses of a
categorical distribution. Weights with a nonzero finite total
[normalize](##Convexity.StdSimplex.normalize_weights) to one. Counts have
[their greatest likelihood](##Convexity.StdSimplex.prod_weights_pow_le_normalize) under their
relative frequencies and, unless they are all zero,
[under no other probability vector](##Convexity.StdSimplex.prod_weights_pow_eq_normalize_iff): the
maximum-likelihood estimate of a categorical distribution is the empirical one.

## Implementation notes

`StdSimplex.normalize` is total: weights totalling `0` or `⊤` give the uniform vector.
`StdSimplex.ofFintype` is an `[UPSTREAM]` candidate for
`Mathlib/Geometry/Convex/ConvexSpace/Defs.lean`.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace Convexity.StdSimplex

variable {ι : Type*} [Fintype ι]

/-- The point of the standard simplex with given nonnegative weights summing to one on a finite
type. -/
noncomputable def ofFintype {R : Type*} [PartialOrder R] [Semiring R] (f : ι → R)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∑ i, f i = 1) : StdSimplex R ι where
  weights := Finsupp.equivFunOnFinite.symm f
  nonneg := h0
  total := by rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl, Finsupp.coe_equivFunOnFinite_symm, h1]

@[simp]
theorem ofFintype_weights {R : Type*} [PartialOrder R] [Semiring R] (f : ι → R)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∑ i, f i = 1) (i : ι) : (ofFintype f h0 h1).weights i = f i :=
  rfl

theorem weights_le_one (t : StdSimplex ℝ≥0∞ ι) (i : ι) : t.weights i ≤ 1 :=
  (single_le_sum (f := t.weights) (fun _ _ ↦ zero_le) (mem_univ i)).trans_eq t.total_of_fintype

theorem weights_ne_top (t : StdSimplex ℝ≥0∞ ι) (i : ι) : t.weights i ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (t.weights_le_one i)

/-- The probability vector of a real one. -/
noncomputable def ofReal (t : StdSimplex ℝ ι) : StdSimplex ℝ≥0∞ ι :=
  ofFintype (fun i ↦ .ofReal (t.weights i)) (fun _ ↦ zero_le) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ t.weights_nonneg i, t.total_of_fintype,
      ENNReal.ofReal_one]

@[simp]
theorem ofReal_weights (t : StdSimplex ℝ ι) (i : ι) :
    t.ofReal.weights i = .ofReal (t.weights i) :=
  rfl

/-! ### Normalization -/

section Normalize

variable [Nonempty ι] {w : ι → ℝ≥0∞}

open scoped Classical in
/-- The probability vector proportional to the weights `w`, and the uniform one when the weights
total `0` or `⊤`. -/
noncomputable def normalize (w : ι → ℝ≥0∞) : StdSimplex ℝ≥0∞ ι :=
  ofFintype (fun i ↦ if ∑ j, w j = 0 ∨ ∑ j, w j = ⊤ then (Fintype.card ι : ℝ≥0∞)⁻¹
    else w i / ∑ j, w j) (fun _ ↦ zero_le) <| by
    by_cases h : ∑ j, w j = 0 ∨ ∑ j, w j = ⊤
    · simp only [ite_eq_left h, sum_const, card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)
    · simp only [ite_eq_right h, div_eq_mul_inv, ← sum_mul]
      exact ENNReal.mul_inv_cancel (fun h0 ↦ h (.inl h0)) fun htop ↦ h (.inr htop)

theorem normalize_weights (h0 : ∑ j, w j ≠ 0) (htop : ∑ j, w j ≠ ⊤) (i : ι) :
    (normalize w).weights i = w i / ∑ j, w j := by
  simp [normalize, h0, htop]

theorem normalize_weights_lt_normalize_weights_iff (htop : ∑ j, w j ≠ ⊤) {i j : ι} :
    (normalize w).weights i < (normalize w).weights j ↔ w i < w j := by
  by_cases h0 : ∑ j, w j = 0
  · simp [normalize, h0, sum_eq_zero_iff.mp h0 i (mem_univ _),
      sum_eq_zero_iff.mp h0 j (mem_univ _)]
  · rw [normalize_weights h0 htop, normalize_weights h0 htop]
    exact ENNReal.div_lt_div_iff_left h0 htop

/-! ### Maximum likelihood -/

private theorem prod_normalize_weights_pow (x : ι → ℕ) :
    ∏ i, (normalize fun i ↦ (x i : ℝ≥0∞)).weights i ^ x i =
      ∏ i, ((x i : ℝ≥0∞) / ∑ j, (x j : ℝ≥0∞)) ^ x i := by
  refine prod_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (x i) with h | h
  · simp [h]
  rw [normalize_weights (by
    have := h.trans_le (single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _) (mem_univ i))
    exact_mod_cast this.ne') (by simp [← Nat.cast_sum])]

/-- **Maximum likelihood of a categorical distribution.** Counts have likelihood under a
probability vector at most their likelihood under their relative frequencies. -/
theorem prod_weights_pow_le_normalize (t : StdSimplex ℝ≥0∞ ι) (x : ι → ℕ) :
    ∏ i, t.weights i ^ x i ≤ ∏ i, (normalize fun i ↦ (x i : ℝ≥0∞)).weights i ^ x i :=
  (ENNReal.prod_pow_le_prod_div_sum_pow univ t.total_of_fintype.le x).trans_eq
    (prod_normalize_weights_pow x).symm

/-- **Uniqueness of the maximum-likelihood estimate.** Counts that are not all `0` attain their
greatest likelihood only at their relative frequencies. -/
theorem prod_weights_pow_eq_normalize_iff (t : StdSimplex ℝ≥0∞ ι) {x : ι → ℕ}
    (hx : ∑ i, x i ≠ 0) :
    ∏ i, t.weights i ^ x i = ∏ i, (normalize fun i ↦ (x i : ℝ≥0∞)).weights i ^ x i ↔
      t = normalize fun i ↦ (x i : ℝ≥0∞) := by
  rw [prod_normalize_weights_pow,
    ENNReal.prod_pow_eq_prod_div_sum_pow_iff univ t.total_of_fintype.le hx, ← weights_inj]
  refine ⟨fun h ↦ Finsupp.ext fun i ↦ ?_, fun h i _ ↦ ?_⟩
  · rw [h i (mem_univ i), normalize_weights (by exact_mod_cast hx) (by simp [← Nat.cast_sum])]
  · rw [h, normalize_weights (by exact_mod_cast hx) (by simp [← Nat.cast_sum])]

theorem prod_normalize_weights_pow_ne_zero (x : ι → ℕ) :
    ∏ i, (normalize fun i ↦ (x i : ℝ≥0∞)).weights i ^ x i ≠ 0 := by
  rw [prod_normalize_weights_pow]
  refine prod_ne_zero_iff.mpr fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (x i) with h | h
  · simp [h]
  · exact pow_ne_zero _ (ENNReal.div_ne_zero.mpr
      ⟨by exact_mod_cast h.ne', by simp [← Nat.cast_sum]⟩)

end Normalize

end Convexity.StdSimplex
