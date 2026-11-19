/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Moments.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Probability.Moments.Tilted

/-!
# Tilted measures and the maximum of `s * m - cgf X μ s`  `[UPSTREAM]`

The cumulant-generating function of a real random variable `X` is convex and, at an interior
point `t` of the set where it is finite, has derivative the mean of `X` under
`μ.tilted (t * X ·)`. So for a target mean `m` the concave function `s ↦ s * m - cgf X μ s` [is
greatest at](##ProbabilityTheory.isMaxOn_mul_sub_cgf_iff) such a `t` exactly when the derivative
there is `m`, that is, [when the tilted
measure](##ProbabilityTheory.isMaxOn_mul_sub_cgf_iff_integral_tilted_mul) at `t` has mean `m`: the member of the exponential family of `μ` and `X` that best fits a sample
of mean `m` is the one that reproduces `m`.
-/

public section

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t m : ℝ}

/-- The function `s ↦ s * m - cgf X μ s` is greatest at an interior point `t` exactly when the
derivative of the cumulant-generating function at `t` is `m`. -/
theorem isMaxOn_mul_sub_cgf_iff (ht : t ∈ interior (integrableExpSet X μ)) :
    IsMaxOn (fun s ↦ s * m - cgf X μ s) (integrableExpSet X μ) t ↔ deriv (cgf X μ) t = m := by
  have hd := (analyticAt_cgf ht).differentiableAt.hasDerivAt
  have htS := interior_subset ht
  constructor
  · intro h
    have h0 := (h.isLocalMax (mem_interior_iff_mem_nhds.1 ht)).hasDerivAt_eq_zero
      (((hasDerivAt_id t).mul_const m).sub hd)
    linarith
  · rintro rfl s hs
    change s * deriv (cgf X μ) t - cgf X μ s ≤ t * deriv (cgf X μ) t - cgf X μ t
    rcases lt_trichotomy s t with hst | rfl | hst
    · have := convexOn_cgf.slope_le_of_hasDerivAt hs htS hst hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.2 hst)] at this
      linarith
    · rfl
    · have := convexOn_cgf.le_slope_of_hasDerivAt htS hs hst hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.2 hst)] at this
      linarith

/-- The function `s ↦ s * m - cgf X μ s` is greatest at an interior point `t` exactly when `X`
has mean `m` under the measure tilted at `t`. -/
theorem isMaxOn_mul_sub_cgf_iff_integral_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    IsMaxOn (fun s ↦ s * m - cgf X μ s) (integrableExpSet X μ) t ↔
      (μ.tilted (t * X ·))[X] = m := by
  rw [isMaxOn_mul_sub_cgf_iff ht, integral_tilted_mul_self ht]

end ProbabilityTheory
