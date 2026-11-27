/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

/-!
# The tilted measure with a given mean  `[UPSTREAM]`

For `t` in the interior of `integrableExpSet X μ`, the derivative of `cgf X μ` at `t` is the mean
of `X` under the tilted measure `μ.tilted (t * X ·)`. Hence the function `s ↦ s * m - cgf X μ s`
[attains its maximum](##ProbabilityTheory.isMaxOn_mul_sub_cgf_iff_integral_tilted_mul) at `t` if
and only if `X` has mean `m` under the measure tilted at `t`.

When `m` is the mean of a sample, `s * m - cgf X μ s` is the average log-density of the sample
under `μ.tilted (s * X ·)`, relative to `μ`. So the statement says that the member of this
exponential family of greatest likelihood is the one whose mean is the sample mean.
-/

public section

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t m : ℝ}

/-- For `t` in the interior of `integrableExpSet X μ`, the function `s ↦ s * m - cgf X μ s`
attains its maximum on that set at `t` if and only if `X` has mean `m` under
`μ.tilted (t * X ·)`. -/
theorem isMaxOn_mul_sub_cgf_iff_integral_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    IsMaxOn (fun s ↦ s * m - cgf X μ s) (integrableExpSet X μ) t ↔
      (μ.tilted (t * X ·))[X] = m := by
  rw [isMaxOn_mul_sub_cgf_iff ht, integral_tilted_mul_self ht]

end ProbabilityTheory
