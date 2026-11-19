/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.KullbackLeibler.Tilted
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Probability.Moments.Tilted

/-!
# Convexity of the cumulant-generating function  `[UPSTREAM]`

The moment-generating function of a real random variable `X` [is
log-convex](##ProbabilityTheory.mgf_add_le_rpow_mul_rpow) on the set where it is finite, by
Hölder's inequality, so the cumulant-generating function [is
convex](##ProbabilityTheory.convexOn_cgf) there. Its derivative at `t` is the mean of `X` under
`μ.tilted (t * X ·)`, so for a target mean `m` the concave function `s ↦ s * m - cgf X μ s` [is
greatest at](##ProbabilityTheory.isMaxOn_mul_sub_cgf_iff_integral_tilted_mul) an interior `t`
exactly when the tilted measure at `t` has mean `m`: the member of the exponential family of `μ`
and `X` that best fits a sample of mean `m` is the one that reproduces `m`. The value of that
function at such a `t` [is](##ProbabilityTheory.toReal_klDiv_tilted_mul_left_self) the divergence
of the tilted measure from `μ`.
-/

public section

open MeasureTheory Real Set InformationTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {s t a b m : ℝ}

/-- Log-convexity of the moment-generating function, in multiplicative form. -/
theorem mgf_add_le_rpow_mul_rpow (hs : s ∈ integrableExpSet X μ) (ht : t ∈ integrableExpSet X μ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    mgf X μ (a * s + b * t) ≤ mgf X μ s ^ a * mgf X μ t ^ b := by
  have e : HolderConjugate (1 / a) (1 / b) := Real.holderConjugate_one_div ha hb hab
  have hpow {c : ℝ} (hc : 0 < c) (u : ℝ) (ω : Ω) :
      exp (u * X ω) = exp (c * (u * X ω)) ^ (1 / c) := by
    rw [← exp_mul]
    congr 1
    field
  have hLp {c u : ℝ} (hc : 0 < c) (hu : u ∈ integrableExpSet X μ) :
      MemLp (fun ω ↦ exp (c * (u * X ω))) (ENNReal.ofReal (1 / c)) μ := by
    have A : ENNReal.ofReal (1 / c) ≠ 0 := by
      rwa [Ne, ENNReal.ofReal_eq_zero, not_le, one_div_pos]
    rw [← integrable_norm_rpow_iff _ A ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (one_div_nonneg.2 hc.le)]
    · exact hu.congr (ae_of_all _ fun ω ↦ by
        simpa only [norm_of_nonneg (exp_pos _).le] using hpow hc u ω)
    · refine ((hu.1.aemeasurable.pow_const c).congr (ae_of_all _ fun ω ↦ ?_)).aestronglyMeasurable
      simp only [← exp_mul, mul_comm]
  simp only [mgf]
  convert integral_mul_le_Lp_mul_Lq_of_nonneg (f := fun ω ↦ exp (a * (s * X ω)))
    (g := fun ω ↦ exp (b * (t * X ω))) e (ae_of_all _ fun ω ↦ (exp_pos _).le)
    (ae_of_all _ fun ω ↦ (exp_pos _).le) (hLp ha hs) (hLp hb ht) using 1
  · refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only [← exp_add]
    ring_nf
  · rw [one_div_one_div, one_div_one_div]
    congr 2 <;> exact integral_congr_ae (ae_of_all _ fun ω ↦ hpow (by assumption) _ ω)

/-- The cumulant-generating function is convex on the set where the moment-generating function
is finite. -/
theorem convexOn_cgf : ConvexOn ℝ (integrableExpSet X μ) (cgf X μ) := by
  refine ⟨convex_integrableExpSet, fun s hs t ht a b ha hb hab ↦ ?_⟩
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  rcases ha.eq_or_lt with rfl | ha
  · simp [show b = 1 by linarith]
  rcases hb.eq_or_lt with rfl | hb
  · simp [show a = 1 by linarith]
  have hu := convex_integrableExpSet hs ht ha.le hb.le hab
  simp only [smul_eq_mul] at hu ⊢
  have h₁ := mgf_pos' hμ hs
  have h₂ := mgf_pos' hμ ht
  rw [cgf, cgf, cgf, ← log_rpow h₁, ← log_rpow h₂,
    ← log_mul (rpow_pos_of_pos h₁ a).ne' (rpow_pos_of_pos h₂ b).ne']
  exact log_le_log (mgf_pos' hμ hu) (mgf_add_le_rpow_mul_rpow hs ht ha hb hab)

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

/-- The divergence of the measure tilted at `t` from its base measure is `t` times the tilted
mean of `X` less the cumulant-generating function at `t`. -/
theorem toReal_klDiv_tilted_mul_left_self [IsProbabilityMeasure μ]
    (ht : t ∈ interior (integrableExpSet X μ)) :
    (klDiv (μ.tilted (t * X ·)) μ).toReal = t * (μ.tilted (t * X ·))[X] - cgf X μ t := by
  rw [toReal_klDiv_tilted_left_self (((memLp_tilted_mul ht 1).integrable le_rfl).const_mul t)
    (interior_subset ht), integral_const_mul, cgf, mgf]

end ProbabilityTheory
