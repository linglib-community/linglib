/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.Probability.CDF

/-!
# The logistic distribution

The standard logistic distribution is the probability measure on `ℝ` whose distribution function is
the sigmoid `σ x = 1 / (1 + exp (-x))`. It is the Stieltjes measure of `Real.sigmoid`, so [its cdf
is the sigmoid](##ProbabilityTheory.cdf_logisticMeasure_eq). Since the sigmoid is continuous,
strictly monotone and satisfies `σ (-x) = 1 - σ x`, the distribution has no atoms, charges every
nonempty open set and is symmetric about `0`, and [its quantile function is the
log-odds](##ProbabilityTheory.quantile_logisticMeasure) `Real.logit`.

## Implementation notes

Mathlib's distributions on `ℝ` are families with a density with respect to the Lebesgue measure.
This file has the standard member of the logistic family only, built from its distribution function
without the density `σ x * (1 - σ x)`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The standard logistic distribution, the probability measure whose distribution function is the
sigmoid. -/
noncomputable def logisticMeasure : Measure ℝ :=
  StieltjesFunction.measure
    ⟨Real.sigmoid, Real.sigmoid_monotone, fun _ ↦ continuous_sigmoid.continuousWithinAt⟩

instance : IsProbabilityMeasure logisticMeasure :=
  StieltjesFunction.isProbabilityMeasure _ Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop

theorem coe_cdf_logisticMeasure : ⇑(cdf logisticMeasure) = Real.sigmoid :=
  congrArg (⇑) <|
    cdf_measure_stieltjesFunction _ Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop

theorem cdf_logisticMeasure_eq (x : ℝ) : cdf logisticMeasure x = Real.sigmoid x :=
  congrFun coe_cdf_logisticMeasure x

instance : NullSingletonClass logisticMeasure :=
  (continuous_cdf_iff _).1 <| coe_cdf_logisticMeasure ▸ continuous_sigmoid

instance : logisticMeasure.IsOpenPosMeasure :=
  (strictMono_cdf_iff _).1 <| coe_cdf_logisticMeasure ▸ Real.sigmoid_strictMono

instance : logisticMeasure.IsNegInvariant :=
  (isNegInvariant_iff_cdf_neg _).2 fun x ↦ by
    simp only [cdf_logisticMeasure_eq, Real.sigmoid_neg]

/-- The quantile function of the standard logistic distribution is the log-odds. -/
theorem quantile_logisticMeasure {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    quantile logisticMeasure p = Real.logit p := by
  obtain ⟨x, rfl⟩ : p ∈ Set.range Real.sigmoid := Real.range_sigmoid ▸ hp
  rw [← cdf_logisticMeasure_eq, quantile_cdf, cdf_logisticMeasure_eq, Real.logit_sigmoid]

end ProbabilityTheory
