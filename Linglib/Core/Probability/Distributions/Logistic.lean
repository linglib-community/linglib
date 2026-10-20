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
the sigmoid `σ x = 1 / (1 + exp (-x))`. It is the Stieltjes measure of `Real.sigmoid`, so its cdf is
the sigmoid (`cdf_logisticMeasure`) and the log-odds `Real.logit` invert the distribution function
on `(0, 1)`. Since the sigmoid is continuous, strictly monotone and satisfies `σ (-x) = 1 - σ x`,
the distribution has no atoms, charges every nonempty open set and is symmetric about `0`, so the
regularity results of `Linglib/Core/Probability/CDF.lean` apply to it. `[UPSTREAM]` candidate for
`Mathlib/Probability/Distributions/Logistic.lean`.

## Main definitions

* `ProbabilityTheory.logisticMeasure`: the standard logistic distribution.

## Main results

* `ProbabilityTheory.cdf_logisticMeasure`: the cdf of the standard logistic distribution is the
  sigmoid.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The sigmoid as a Stieltjes function. -/
noncomputable def sigmoidStieltjes : StieltjesFunction ℝ where
  toFun := Real.sigmoid
  mono' := Real.sigmoid_monotone
  right_continuous' _ := continuous_sigmoid.continuousWithinAt

@[simp]
theorem sigmoidStieltjes_apply (x : ℝ) : sigmoidStieltjes x = Real.sigmoid x := rfl

/-- The standard logistic distribution, the probability measure whose distribution function is the
sigmoid. -/
noncomputable def logisticMeasure : Measure ℝ := sigmoidStieltjes.measure

instance : IsProbabilityMeasure logisticMeasure :=
  sigmoidStieltjes.isProbabilityMeasure Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop

theorem cdf_logisticMeasure (x : ℝ) : cdf logisticMeasure x = Real.sigmoid x := by
  rw [logisticMeasure,
    cdf_measure_stieltjesFunction _ Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop,
    sigmoidStieltjes_apply]

instance : NullSingletonClass logisticMeasure :=
  sigmoidStieltjes.continuous_iff_nullSingletonClass.1 continuous_sigmoid

instance : logisticMeasure.IsOpenPosMeasure :=
  sigmoidStieltjes.strictMono_iff_isOpenPosMeasure.1 Real.sigmoid_strictMono

instance : logisticMeasure.IsNegInvariant :=
  (isNegInvariant_iff_cdf_neg _).2 fun x ↦ by simp only [cdf_logisticMeasure, Real.sigmoid_neg]

end ProbabilityTheory
