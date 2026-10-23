/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.UniformOn
public import Mathlib.Algebra.Order.Monovary
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev's integral inequality and empirical covariance  `[UPSTREAM]`

Two real random variables that monovary have nonnegative covariance, and two that antivary
have nonpositive covariance. On a finite measure the statement is
`(∫ X ∂μ) * ∫ Y ∂μ ≤ μ.real univ * ∫ X * Y ∂μ`, the integral form of Chebyshev's sum
inequality (`MonovaryOn.sum_mul_sum_le_card_mul_sum`); on a probability measure it reads
`0 ≤ cov[X, Y; μ]`.

Under the uniform measure on a finite type the covariance is the sample covariance, the mean of
the products less the product of the means, and it is positive exactly when the sum of products
exceeds the product of the sums divided by the sample size.

## Main declarations

* `Monovary.integral_mul_integral_le_measureReal_univ_mul_integral`,
  `Antivary.measureReal_univ_mul_integral_le_integral_mul_integral`: Chebyshev's integral
  inequality on a finite measure and its dual.
* `Monovary.covariance_nonneg`, `Antivary.covariance_nonpos`: the covariance forms.
* `covariance_uniformOn_univ`, `covariance_uniformOn_univ_pos_iff`: the sample covariance under
  the uniform measure on a finite type and the sign of its numerator.

## Implementation notes

The proof integrates `0 ≤ (X ω - X ω') * (Y ω - Y ω')`, pointwise nonnegative by
`Monovary.sub_mul_sub_nonneg`, over the product measure `μ.prod μ`, where it expands to twice
the covariance defect. The dual follows by negating `X`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ}

section FiniteMeasure

variable [IsFiniteMeasure μ] (hX : Integrable X μ) (hY : Integrable Y μ)
  (hXY : Integrable (X * Y) μ)
include hX hY hXY

theorem Monovary.integral_mul_integral_le_measureReal_univ_mul_integral (h : Monovary X Y) :
    (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ ≤ μ.real Set.univ * ∫ ω, X ω * Y ω ∂μ := by
  have h₁ := hXY.mul_prod (μ := μ) (ν := μ) (integrable_const (1 : ℝ))
  have h₂ := hX.mul_prod (μ := μ) (ν := μ) hY
  have h₃ := hY.mul_prod (μ := μ) (ν := μ) hX
  have h₄ := (integrable_const (1 : ℝ)).mul_prod (μ := μ) (ν := μ) hXY
  have key : ∫ z, (X z.1 - X z.2) * (Y z.1 - Y z.2) ∂(μ.prod μ) =
      2 * (μ.real Set.univ * ∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ) := by
    have e : (fun z : Ω × Ω ↦ (X z.1 - X z.2) * (Y z.1 - Y z.2)) = fun z ↦
        ((X * Y) z.1 * (1 : Ω → ℝ) z.2 - X z.1 * Y z.2) -
          (Y z.1 * X z.2 - (1 : Ω → ℝ) z.1 * (X * Y) z.2) := by
      ext z; simp only [Pi.mul_apply, Pi.one_apply]; ring
    rw [e, integral_sub, integral_sub, integral_sub, integral_prod_mul, integral_prod_mul,
      integral_prod_mul, integral_prod_mul]
    · simp only [Pi.mul_apply, Pi.one_apply, integral_const, smul_eq_mul, mul_one]; ring
    all_goals first | exact h₁ | exact h₂ | exact h₃ | exact h₄ | exact h₁.sub h₂ | exact h₃.sub h₄
  have h₀ : 0 ≤ ∫ z, (X z.1 - X z.2) * (Y z.1 - Y z.2) ∂(μ.prod μ) :=
    integral_nonneg fun z ↦ h.sub_mul_sub_nonneg z.2 z.1
  linarith

theorem Antivary.measureReal_univ_mul_integral_le_integral_mul_integral (h : Antivary X Y) :
    μ.real Set.univ * ∫ ω, X ω * Y ω ∂μ ≤ (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
  have := (monovary_neg_left.2 h).integral_mul_integral_le_measureReal_univ_mul_integral
    hX.neg hY (by simpa only [neg_mul] using hXY.neg)
  simpa only [Pi.neg_apply, neg_mul, integral_neg, mul_neg, neg_le_neg_iff] using this

end FiniteMeasure

section ProbabilityMeasure

open ProbabilityTheory

variable [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
include hX hY

theorem Monovary.covariance_nonneg (h : Monovary X Y) : 0 ≤ cov[X, Y; μ] := by
  rw [covariance_eq_sub hX hY, sub_nonneg]
  simpa [probReal_univ] using h.integral_mul_integral_le_measureReal_univ_mul_integral
    (hX.integrable one_le_two) (hY.integrable one_le_two) (hX.integrable_mul hY)

theorem Antivary.covariance_nonpos (h : Antivary X Y) : cov[X, Y; μ] ≤ 0 := by
  rw [covariance_eq_sub hX hY, sub_nonpos]
  simpa [probReal_univ] using h.measureReal_univ_mul_integral_le_integral_mul_integral
    (hX.integrable one_le_two) (hY.integrable one_le_two) (hX.integrable_mul hY)

end ProbabilityMeasure

namespace ProbabilityTheory

section UniformOn

variable [MeasurableSingletonClass Ω] [Fintype Ω]

theorem integral_uniformOn_univ (f : Ω → ℝ) :
    ∫ ω, f ω ∂(uniformOn Set.univ) = (∑ ω, f ω) / Fintype.card Ω := by
  rw [integral_fintype .of_finite, div_eq_inv_mul, Finset.mul_sum]
  simp_rw [uniformOn_univ_real_singleton, smul_eq_mul]

variable [Nonempty Ω] (X Y)

theorem covariance_uniformOn_univ :
    cov[X, Y; uniformOn Set.univ] = (∑ ω, X ω * Y ω) / Fintype.card Ω
      - (∑ ω, X ω) / Fintype.card Ω * ((∑ ω, Y ω) / Fintype.card Ω) := by
  rw [covariance_eq_sub .of_discrete .of_discrete, integral_uniformOn_univ,
    integral_uniformOn_univ, integral_uniformOn_univ]
  rfl

theorem covariance_uniformOn_univ_pos_iff :
    0 < cov[X, Y; uniformOn Set.univ] ↔
      (∑ ω, X ω) * ∑ ω, Y ω < Fintype.card Ω * ∑ ω, X ω * Y ω := by
  have hn : (0 : ℝ) < Fintype.card Ω := by positivity
  rw [covariance_uniformOn_univ, sub_pos, div_mul_div_comm, div_lt_div_iff₀ (by positivity) hn]
  constructor <;> intro h <;> nlinarith

end UniformOn

end ProbabilityTheory
