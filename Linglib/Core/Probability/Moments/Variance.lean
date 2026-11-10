/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# The second moment about a point  `[UPSTREAM]`

The mean squared deviation of a real random variable from a point `c` is its variance plus the
squared distance of its mean from `c`. At `c = 0` this is `ProbabilityTheory.variance_eq_sub`,
and in general it is the decomposition of a mean squared error into variance and squared bias.
-/

public section

open MeasureTheory

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

end ProbabilityTheory
