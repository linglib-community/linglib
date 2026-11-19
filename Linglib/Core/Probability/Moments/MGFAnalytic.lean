/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Moments.Basic
public import Linglib.Core.Analysis.Convex.Deriv
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Maximizing `s * m - cgf X μ s`  `[UPSTREAM]`

Fix a real number `m`. The function `s ↦ s * m - cgf X μ s` is concave on
`integrableExpSet X μ`, because the cumulant-generating function is convex there. At a point `t`
in the interior of that set, it [attains its maximum](##ProbabilityTheory.isMaxOn_mul_sub_cgf_iff)
if and only if `deriv (cgf X μ) t = m`.
-/

public section

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t m : ℝ}

/-- For `t` in the interior of `integrableExpSet X μ`, the function `s ↦ s * m - cgf X μ s`
attains its maximum on that set at `t` if and only if `deriv (cgf X μ) t = m`. -/
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
    have := convexOn_cgf.apply_sub_le_sub_of_hasFDerivAt htS hs hd.hasFDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
    change s * deriv (cgf X μ) t - cgf X μ s ≤ t * deriv (cgf X μ) t - cgf X μ t
    linarith

end ProbabilityTheory
