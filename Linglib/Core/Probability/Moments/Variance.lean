/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# The second moment about a point and the variance of a mixture  `[UPSTREAM]`

The mean squared deviation of a real random variable from a point `c` is its variance plus the
squared distance of its mean from `c`. At `c = 0` this is `ProbabilityTheory.variance_eq_sub`,
and in general it is the decomposition of a mean squared error into variance and squared bias.
Applied to each component of a mixture of two laws about the mixture's mean, it gives the
variance of the mixture: the mixture of the variances plus the weighted squared distance between
the two means.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}

/-- The second moment of `X` about `c` is the variance of `X` plus the squared distance of its
mean from `c`. -/
theorem integral_sub_const_sq (hX : MemLp X 2 μ) (c : ℝ) :
    ∫ ω, (X ω - c) ^ 2 ∂μ = Var[X; μ] + (μ[X] - c) ^ 2 := by
  have h := variance_eq_sub (hX.sub (memLp_const c))
  rw [show X - (fun _ ↦ c) = fun ω ↦ X ω - c from rfl,
    variance_sub_const hX.aestronglyMeasurable,
    integral_sub (hX.integrable one_le_two) (integrable_const c)] at h
  simp only [Pi.pow_apply, integral_const, probReal_univ, one_smul] at h
  linarith

variable {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- The variance under a mixture of two laws is the mixture of their variances plus the weighted
squared distance between their means. -/
theorem variance_smul_add_smul_measure {a b : ℝ≥0} (hab : a + b = 1) (hμ : MemLp X 2 μ)
    (hν : MemLp X 2 ν) :
    Var[X; a • μ + b • ν] = a * Var[X; μ] + b * Var[X; ν] + a * b * (μ[X] - ν[X]) ^ 2 := by
  have hb : (b : ℝ) = 1 - a := by rw [← NNReal.coe_one, ← hab]; push_cast; ring
  have key (f : Ω → ℝ) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
      ∫ ω, f ω ∂(a • μ + b • ν) = a * ∫ ω, f ω ∂μ + b * ∫ ω, f ω ∂ν := by
    rw [integral_add_measure hfμ.smul_measure_nnreal hfν.smul_measure_nnreal,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
  rw [variance_eq_integral
      ((hμ.aemeasurable.smul_measure _).add_measure (hν.aemeasurable.smul_measure _)),
    key (fun ω ↦ (X ω - _) ^ 2) (hμ.sub (memLp_const _)).integrable_sq
      (hν.sub (memLp_const _)).integrable_sq,
    integral_sub_const_sq hμ, integral_sub_const_sq hν,
    key _ (hμ.integrable one_le_two) (hν.integrable one_le_two), hb]
  ring

end ProbabilityTheory
