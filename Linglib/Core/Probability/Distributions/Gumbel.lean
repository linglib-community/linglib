/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.CDF

/-!
# Gumbel distributions over ℝ

The Gumbel distribution with location `μ` and scale `β`, the type I extreme value distribution, has
distribution function `exp (-exp (-((x - μ) / β)))`. Like `gaussianReal` and `cauchyMeasure`, the
measure takes its scale in `ℝ≥0` and is `dirac μ` at scale zero. The family is max-stable: the
maximum of independent Gumbel variables of a common scale is Gumbel with that scale.
`[UPSTREAM]` candidate for `Mathlib/Probability/Distributions/Gumbel.lean`.

## Main definitions

* `gumbelPDFReal`: the function `μ β x ↦ β⁻¹ * exp (-((x - μ) / β)) * exp (-exp (-((x - μ) / β)))`,
  the probability density function of the Gumbel distribution with location `μ` and scale `β`
  (when `β ≠ 0`).
* `gumbelPDF`: `ℝ≥0∞`-valued pdf, `gumbelPDF μ β x = ENNReal.ofReal (gumbelPDFReal μ β x)`.
* `gumbelMeasure`: the Gumbel measure on `ℝ`. If `β = 0` it is `dirac μ`, otherwise the measure
  with density `gumbelPDF μ β` with respect to the Lebesgue measure.

## Main results

* `cdf_gumbelMeasure_eq`: the cdf is `exp (-exp (-((x - μ) / β)))`.
* `gumbelPDFReal_eq_mul_cdf`: the pdf is the cdf times the reverse hazard rate
  `β⁻¹ * exp (-((x - μ) / β))`.
* `prod_cdf_gumbelMeasure`: max-stability. The product of the cdfs with locations `u j` and a
  common scale `β` is the cdf with location `β * log (∑ j, exp (u j / β))`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {β : ℝ≥0}

section GumbelPDF

/-- The pdf of the Gumbel distribution with location `μ` and scale `β`. -/
noncomputable def gumbelPDFReal (μ : ℝ) (β : ℝ≥0) (x : ℝ) : ℝ :=
  (β : ℝ)⁻¹ * exp (-((x - μ) / β)) * exp (-exp (-((x - μ) / β)))

@[simp]
lemma gumbelPDFReal_zero_scale (μ : ℝ) : gumbelPDFReal μ 0 = 0 := by
  ext; simp [gumbelPDFReal]

lemma gumbelPDFReal_nonneg (μ : ℝ) (β : ℝ≥0) (x : ℝ) : 0 ≤ gumbelPDFReal μ β x := by
  unfold gumbelPDFReal; positivity

@[fun_prop]
lemma continuous_gumbelPDFReal (μ : ℝ) (β : ℝ≥0) : Continuous (gumbelPDFReal μ β) := by
  unfold gumbelPDFReal; fun_prop

@[fun_prop]
lemma measurable_gumbelPDFReal (μ : ℝ) (β : ℝ≥0) : Measurable (gumbelPDFReal μ β) :=
  (continuous_gumbelPDFReal μ β).measurable

private lemma hasDerivAt_gumbelCDF (μ : ℝ) (β : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun y ↦ exp (-exp (-((y - μ) / β)))) (gumbelPDFReal μ β x) x :=
  (((hasDerivAt_id x).sub_const μ).div_const (β : ℝ)).neg.exp.neg.exp.congr_deriv <| by
    simp only [gumbelPDFReal, Pi.neg_apply, id]; ring

private lemma tendsto_div_atTop (μ : ℝ) (hβ : β ≠ 0) :
    Tendsto (fun y : ℝ ↦ (y - μ) / β) atTop atTop :=
  (tendsto_atTop_add_const_right _ (-μ) tendsto_id).atTop_div_const (by positivity)

private lemma tendsto_div_atBot (μ : ℝ) (hβ : β ≠ 0) :
    Tendsto (fun y : ℝ ↦ (y - μ) / β) atBot atBot :=
  (tendsto_atBot_add_const_right _ (-μ) tendsto_id).atBot_div_const (by positivity)

private lemma tendsto_gumbelCDF_atTop (μ : ℝ) (hβ : β ≠ 0) :
    Tendsto (fun y ↦ exp (-exp (-((y - μ) / β)))) atTop (𝓝 1) := by
  have h : Tendsto (fun y ↦ -exp (-((y - μ) / β))) atTop (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_div_atTop μ hβ))).neg
  simpa [Function.comp_def] using (continuous_exp.tendsto 0).comp h

private lemma tendsto_gumbelCDF_atBot (μ : ℝ) (hβ : β ≠ 0) :
    Tendsto (fun y ↦ exp (-exp (-((y - μ) / β)))) atBot (𝓝 0) :=
  tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <| tendsto_exp_atTop.comp <|
    tendsto_neg_atBot_atTop.comp (tendsto_div_atBot μ hβ)

@[fun_prop]
lemma integrable_gumbelPDFReal (μ : ℝ) (β : ℝ≥0) : Integrable (gumbelPDFReal μ β) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [gumbelPDFReal_zero_scale]; exact integrable_zero _ _ _
  refine integrable_of_intervalIntegral_norm_tendsto 1
    (fun _ ↦ (continuous_gumbelPDFReal μ β).integrableOn_Ioc) tendsto_neg_atTop_atBot tendsto_id ?_
  simp_rw [Real.norm_of_nonneg (gumbelPDFReal_nonneg μ β _), id,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_gumbelCDF μ β x)
      ((continuous_gumbelPDFReal μ β).intervalIntegrable _ _)]
  simpa using (tendsto_gumbelCDF_atTop μ hβ).sub
    ((tendsto_gumbelCDF_atBot μ hβ).comp tendsto_neg_atTop_atBot)

lemma integral_gumbelPDFReal_eq_one (μ : ℝ) (hβ : β ≠ 0) : ∫ x, gumbelPDFReal μ β x = 1 := by
  simpa using integral_of_hasDerivAt_of_tendsto (hasDerivAt_gumbelCDF μ β)
    (integrable_gumbelPDFReal μ β) (tendsto_gumbelCDF_atBot μ hβ) (tendsto_gumbelCDF_atTop μ hβ)

/-- The pdf of the Gumbel distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def gumbelPDF (μ : ℝ) (β : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gumbelPDFReal μ β x)

@[fun_prop]
lemma measurable_gumbelPDF (μ : ℝ) (β : ℝ≥0) : Measurable (gumbelPDF μ β) :=
  (measurable_gumbelPDFReal μ β).ennreal_ofReal

@[simp]
lemma lintegral_gumbelPDF_eq_one (μ : ℝ) (hβ : β ≠ 0) : ∫⁻ x, gumbelPDF μ β x = 1 := by
  unfold gumbelPDF
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gumbelPDFReal μ β)
    (ae_of_all _ (gumbelPDFReal_nonneg μ β)), integral_gumbelPDFReal_eq_one μ hβ,
    ENNReal.ofReal_one]

end GumbelPDF

section GumbelMeasure

/-- The Gumbel distribution on `ℝ` with location `μ` and scale `β`. -/
noncomputable def gumbelMeasure (μ : ℝ) (β : ℝ≥0) : Measure ℝ :=
  if β = 0 then Measure.dirac μ else volume.withDensity (gumbelPDF μ β)

lemma gumbelMeasure_of_scale_ne_zero (μ : ℝ) (hβ : β ≠ 0) :
    gumbelMeasure μ β = volume.withDensity (gumbelPDF μ β) := ite_eq_right hβ

@[simp]
lemma gumbelMeasure_zero_scale (μ : ℝ) : gumbelMeasure μ 0 = Measure.dirac μ := ite_eq_left rfl

instance (μ : ℝ) (β : ℝ≥0) : IsProbabilityMeasure (gumbelMeasure μ β) where
  measure_univ := by by_cases h : β = 0 <;> simp [gumbelMeasure_of_scale_ne_zero, h]

lemma nullSingletonClass_gumbelMeasure (μ : ℝ) (hβ : β ≠ 0) :
    NullSingletonClass (gumbelMeasure μ β) := by
  rw [gumbelMeasure_of_scale_ne_zero μ hβ]; infer_instance

/-- The cdf of the Gumbel distribution is `exp (-exp (-((x - μ) / β)))`. -/
lemma cdf_gumbelMeasure_eq (μ : ℝ) (hβ : β ≠ 0) (x : ℝ) :
    cdf (gumbelMeasure μ β) x = exp (-exp (-((x - μ) / β))) := by
  have h : cdf (gumbelMeasure μ β) x = ∫ y in Iic x, gumbelPDFReal μ β y := by
    rw [cdf_eq_real, gumbelMeasure_of_scale_ne_zero μ hβ, measureReal_def,
      withDensity_apply _ measurableSet_Iic]
    exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gumbelPDFReal_nonneg μ β))
      (by fun_prop)).symm
  rw [h, integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ ↦ hasDerivAt_gumbelCDF μ β y)
    (integrable_gumbelPDFReal μ β).integrableOn (tendsto_gumbelCDF_atBot μ hβ), sub_zero]

/-- The pdf of the Gumbel distribution is its cdf times the reverse hazard rate
`β⁻¹ * exp (-((x - μ) / β))`. -/
lemma gumbelPDFReal_eq_mul_cdf (μ : ℝ) (hβ : β ≠ 0) (x : ℝ) :
    gumbelPDFReal μ β x = (β : ℝ)⁻¹ * exp (-((x - μ) / β)) * cdf (gumbelMeasure μ β) x := by
  rw [cdf_gumbelMeasure_eq μ hβ, gumbelPDFReal]

/-- **Max-stability** of the Gumbel family. The product of the cdfs of Gumbel distributions with
locations `u j` and a common scale `β` is the cdf of the Gumbel distribution with location
`β * log (∑ j ∈ s, exp (u j / β))` and scale `β`. -/
theorem prod_cdf_gumbelMeasure {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (u : ι → ℝ)
    (hβ : β ≠ 0) (x : ℝ) :
    ∏ j ∈ s, cdf (gumbelMeasure (u j) β) x =
      cdf (gumbelMeasure (β * log (∑ j ∈ s, exp (u j / β))) β) x := by
  have h (a : ℝ) : exp (-((x - a) / β)) = exp (a / β) * exp (-(x / β)) := by
    rw [← exp_add]; congr 1; ring
  simp only [cdf_gumbelMeasure_eq _ hβ, ← exp_sum, Finset.sum_neg_distrib, h, ← Finset.sum_mul,
    mul_div_cancel_left₀ _ (NNReal.coe_ne_zero.2 hβ),
    exp_log (Finset.sum_pos (fun _ _ ↦ exp_pos _) hs)]

end GumbelMeasure

end ProbabilityTheory
