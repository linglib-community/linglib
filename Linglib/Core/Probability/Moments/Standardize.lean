/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Standardized random variables  `[UPSTREAM]`

The standardization of a real random variable `X` under a measure `μ` is its deviation from the
mean in standard deviations, `(X - μ[X]) / √Var[X; μ]`; under the uniform measure on a finite
set of observations these are the z-scores. Standardization keeps the order of the values,
centres them, scales them to unit variance, and forgets any positive affine change of units.

## Main definitions

* `ProbabilityTheory.standardize`: the standardized random variable.

## Main statements

* `integral_standardize`, `variance_standardize`: standardized values have mean `0` and, when
  `X` is not almost surely constant, variance `1`.
* `standardize_const_mul_add_const`: standardization is invariant under `X ↦ a * X + b` for
  `0 < a`.
* `sign_integral_standardize`: under a subpopulation `ν ≪ μ` the mean standardized value has the
  sign of `ν[X] - μ[X]`.

## Implementation notes

The order lemmas assume `0 < Var[X; μ]`, as mathlib's division lemmas assume a positive
divisor; when the variance is `0` the standardization is constantly `0`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ}

/-- The standardization of `X` under `μ` is its deviation from the mean in standard deviations. -/
noncomputable def standardize (X : Ω → ℝ) (μ : Measure Ω) : Ω → ℝ :=
  fun ω ↦ (X ω - μ[X]) / √Var[X; μ]

theorem standardize_apply (ω : Ω) : standardize X μ ω = (X ω - μ[X]) / √Var[X; μ] := rfl

section Order

variable (h : 0 < Var[X; μ]) {ω ω' : Ω}
include h

theorem standardize_le_standardize_iff : standardize X μ ω ≤ standardize X μ ω' ↔ X ω ≤ X ω' := by
  simp only [standardize, div_le_div_iff_of_pos_right (Real.sqrt_pos.2 h), sub_le_sub_iff_right]

theorem standardize_lt_standardize_iff : standardize X μ ω < standardize X μ ω' ↔ X ω < X ω' := by
  simp only [standardize, div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 h), sub_lt_sub_iff_right]

theorem one_lt_standardize_iff : 1 < standardize X μ ω ↔ μ[X] + √Var[X; μ] < X ω := by
  rw [standardize, lt_div_iff₀ (Real.sqrt_pos.2 h), one_mul, lt_sub_iff_add_lt']

theorem standardize_neg_iff : standardize X μ ω < 0 ↔ X ω < μ[X] := by
  rw [standardize, div_lt_iff₀ (Real.sqrt_pos.2 h), zero_mul, sub_neg]

end Order

theorem standardize_const_mul_add_const [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) {a : ℝ}
    (ha : 0 < a) (b : ℝ) : standardize (fun ω ↦ a * X ω + b) μ = standardize X μ := by
  ext ω
  rw [standardize, standardize, variance_add_const (hX.aestronglyMeasurable.const_mul a) b,
    variance_const_mul, integral_add ((hX.integrable one_le_two).const_mul a) (integrable_const b),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    Real.sqrt_mul' _ (variance_nonneg _ _), Real.sqrt_sq ha.le,
    show a * X ω + b - (a * μ[X] + b) = a * (X ω - μ[X]) by ring, mul_div_mul_left _ _ ha.ne']

theorem integral_standardize_eq [IsProbabilityMeasure ν] (hX : Integrable X ν) :
    ν[standardize X μ] = (ν[X] - μ[X]) / √Var[X; μ] := by
  simp only [standardize_apply]
  rw [integral_div, integral_sub hX (integrable_const _), integral_const, probReal_univ, one_smul]

variable [IsProbabilityMeasure μ] (hX : MemLp X 2 μ)
include hX

theorem integral_standardize : μ[standardize X μ] = 0 := by
  rw [integral_standardize_eq (hX.integrable one_le_two), sub_self, zero_div]

theorem variance_standardize (h : 0 < Var[X; μ]) : Var[standardize X μ; μ] = 1 := by
  have : standardize X μ = fun ω ↦ (√Var[X; μ])⁻¹ * (X ω - μ[X]) := by
    ext ω; rw [standardize, div_eq_inv_mul]
  rw [this, variance_const_mul, variance_sub_const hX.aestronglyMeasurable, inv_pow,
    Real.sq_sqrt (variance_nonneg _ _), inv_mul_cancel₀ h.ne']

theorem sign_integral_standardize [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (hXν : Integrable X ν) :
    SignType.sign ν[standardize X μ] = SignType.sign (ν[X] - μ[X]) := by
  rw [integral_standardize_eq hXν]
  rcases (variance_nonneg X μ).eq_or_lt with h | h
  · have hae : ∀ᵐ ω ∂ν, X ω = μ[X] := hνμ.ae_le (ae_eq_integral_of_variance_eq_zero hX h.symm)
    rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul, ← h]
    simp
  · rw [div_eq_mul_inv, sign_mul, sign_pos (inv_pos.2 (Real.sqrt_pos.2 h)), mul_one]

end ProbabilityTheory
