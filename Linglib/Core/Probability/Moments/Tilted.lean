/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

/-!
# The tilted measure of a given mean  `[UPSTREAM]`

The derivative of the cumulant-generating function of `X` at an interior point `t` is the mean of
`X` under `μ.tilted (t * X ·)`. So for a target mean `m` the function `s ↦ s * m - cgf X μ s` [is
greatest at](##ProbabilityTheory.isMaxOn_mul_sub_cgf_iff_integral_tilted_mul) `t` exactly when
the tilted measure at `t` has mean `m`: the member of the exponential family of `μ` and `X` that
best fits a sample of mean `m` is the one that reproduces `m`.
-/

public section

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t m : ℝ}

/-- The function `s ↦ s * m - cgf X μ s` is greatest at an interior point `t` exactly when `X`
has mean `m` under the measure tilted at `t`. -/
theorem isMaxOn_mul_sub_cgf_iff_integral_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    IsMaxOn (fun s ↦ s * m - cgf X μ s) (integrableExpSet X μ) t ↔
      (μ.tilted (t * X ·))[X] = m := by
  rw [isMaxOn_mul_sub_cgf_iff ht, integral_tilted_mul_self ht]

end ProbabilityTheory
