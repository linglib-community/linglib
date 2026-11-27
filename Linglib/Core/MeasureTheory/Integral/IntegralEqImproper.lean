/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The integral of a nonnegative derivative over the real line

A real function with a nonnegative derivative everywhere and limits at both infinities has an
integrable derivative, whose integral is the difference of the limits. Mathlib has the half-line
versions `integrableOn_Ioi_deriv_of_nonneg` and `integral_Ioi_of_hasDerivAt_of_nonneg`.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`.
-/

public section

open Filter Topology

namespace MeasureTheory

variable {g g' : ℝ → ℝ} {m n : ℝ}

/-- When a function has limits at both infinities and its derivative is nonnegative, the derivative
is integrable. -/
theorem integrable_deriv_of_nonneg (hderiv : ∀ x, HasDerivAt g (g' x) x) (g'pos : 0 ≤ g')
    (hbot : Tendsto g atBot (𝓝 m)) (htop : Tendsto g atTop (𝓝 n)) : Integrable g' := by
  have hint (a b : ℝ) : IntervalIntegrable g' volume a b :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt) (fun x _ ↦ hderiv x)
      fun x _ ↦ g'pos x
  refine integrable_of_intervalIntegral_norm_tendsto (n - m) (a := fun k : ℝ ↦ -k) (b := id)
    (fun k ↦ (hint (-k) k).1) tendsto_neg_atTop_atBot tendsto_id ?_
  simp_rw [Real.norm_of_nonneg (g'pos _), id,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x) (hint _ _)]
  exact htop.sub (hbot.comp tendsto_neg_atTop_atBot)

/-- When a function has limits `m` and `n` at the two infinities and its derivative is nonnegative,
the integral of the derivative is `n - m`. -/
theorem integral_of_hasDerivAt_of_nonneg (hderiv : ∀ x, HasDerivAt g (g' x) x) (g'pos : 0 ≤ g')
    (hbot : Tendsto g atBot (𝓝 m)) (htop : Tendsto g atTop (𝓝 n)) : ∫ x, g' x = n - m :=
  integral_of_hasDerivAt_of_tendsto hderiv (integrable_deriv_of_nonneg hderiv g'pos hbot htop)
    hbot htop

end MeasureTheory
