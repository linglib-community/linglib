module

public import Linglib.Core.Probability.Choice.RandomUtility
public import Linglib.Core.Probability.Distributions.Gaussian
public import Linglib.Core.Probability.Distributions.Logistic

/-!
# Signal detection theory

In signal detection theory a trial holds a signal or only noise, and the observer responds "yes"
when its observation exceeds a criterion `k`. An experiment is a kernel `P : Kernel Bool ℝ` from
the state of the trial to the law of the observation; the *hit rate* and the *false-alarm rate* of
`k` are the masses that the signal law and the noise law give to `(k, ∞)`. A *location experiment*
shifts a noise law `ν` by `δ / 2` on signal trials and by `-(δ / 2)` on noise trials, so that the
sensitivity `δ` is the distance between the two laws. The normal model takes `ν` standard normal,
and Luce's Choice Theory takes it logistic ([macmillan-creelman-2005], ch. 4, p. 98).

## Main definitions

* `hitRate`, `falseAlarmRate`: the response rates of a criterion.
* `forcedChoice`: the proportion correct of a forced-choice task.
* `locationExperiment`: the experiment of a noise law at a sensitivity.

## Main results

* `forcedChoice_eq_lintegral`: the forced-choice proportion correct as an integral (area theorem).
* `hitRate_eq_falseAlarmRate_sub`: the hit rate of `k` is the false-alarm rate of `k - δ`.
* `hitRate_locationExperiment_eq_cdf`: the rates under a symmetric noise law without atoms.
* `falseAlarmRate_lt_hitRate`: at positive sensitivity the hit rate exceeds the false-alarm rate.
* `probit_hitRate_sub_probit_falseAlarmRate`: in the normal model `z(H) = z(F) + d'`.
* `forcedChoice_one_gaussianReal`: in the normal model the 2AFC proportion correct is `Φ (d' / √2)`.
* `logit_hitRate_sub_logit_falseAlarmRate`: in the logistic model `δ` is a difference of log-odds.

## Implementation notes

The forced-choice observer picks the interval with the largest observation, where
[green-swets-1966] (p. 46) pick the one with the largest likelihood ratio; the two agree when the
likelihood ratio increases with the observation, as in the normal model. Page numbers of
[green-swets-1966] are those of the 1988 reprint. The theory stays in this layer with a single
consumer because the study of [luce-1959] cannot import a study of the later [green-swets-1966].

## TODO

* The slope of the receiver operating characteristic at a criterion is the likelihood ratio there
  ([macmillan-creelman-2005], ch. 2); for the normal model this needs the derivative of `Φ`.
* The optimal criterion is the Bayes estimator of the experiment under 0-1 loss, and a larger
  sensitivity gives a more informative experiment in the order of
  `Linglib/Core/Probability/Decision/Blackwell.lean`.
* Luce's axiom-1 forced choice (section 2.E) is a logistic Yes-No model at twice the
  sensitivity, which is not the forced choice of the logistic model: the difference of two logistic
  observations is not logistic.

## References

* [macmillan-creelman-2005]
* [green-swets-1966]
* [luce-1959]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SignalDetection

/-! ### Response rates and forced choice -/

section Experiment

variable (P : Kernel Bool ℝ) (k : ℝ)

/-- The hit rate of the criterion `k` is the probability that the observation on a signal trial
exceeds `k`, so that the observer responds "yes". -/
noncomputable def hitRate : ℝ := (P true).real (Ioi k)

/-- The false-alarm rate of the criterion `k` is the probability that the observation on a noise
trial exceeds `k`. -/
noncomputable def falseAlarmRate : ℝ := (P false).real (Ioi k)

/-- The proportion correct in a forced-choice task with one signal interval and `n` noise
intervals, when the observer picks the interval with the largest observation. It is the choice
probability of the signal interval in the random utility model of the intervals' laws. -/
noncomputable def forcedChoice (n : ℕ) : ℝ≥0∞ :=
  choiceProb (Measure.pi fun j : Fin (n + 1) ↦ P (decide (j = 0))) 0

/-- The forced-choice proportion correct is the probability that all `n` noise observations fall
below the signal observation `k`, integrated over `k` ([green-swets-1966], eqs. (2.7) and (2.13),
p. 47). With one noise interval it is the area under the yes-no receiver operating
characteristic, the hit rate integrated over the false-alarm rate. -/
theorem forcedChoice_eq_lintegral [IsFiniteKernel P] (n : ℕ) :
    forcedChoice P n = ∫⁻ k, P false (Iio k) ^ n ∂(P true) := by
  rw [forcedChoice, choiceProb_pi_eq_lintegral]
  refine lintegral_congr fun k ↦ ?_
  rw [Finset.prod_congr rfl fun j hj ↦ by rw [decide_eq_false (Finset.ne_of_mem_erase hj)],
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]

end Experiment

/-! ### Location experiments -/

section Location

variable (ν : Measure ℝ) (δ : ℝ)

/-- In the location experiment of a noise law `ν` at sensitivity `δ`, the observation is `ν` shifted
by `δ / 2` on signal trials and by `-(δ / 2)` on noise trials. -/
noncomputable def locationExperiment : Kernel Bool ℝ :=
  Kernel.ofFunOfCountable fun b ↦ ν.map (· + if b then δ / 2 else -(δ / 2))

theorem locationExperiment_apply (b : Bool) :
    locationExperiment ν δ b = ν.map (· + if b then δ / 2 else -(δ / 2)) := rfl

variable {ν δ}

private theorem locationExperiment_real_Ioi (b : Bool) (k : ℝ) :
    (locationExperiment ν δ b).real (Ioi k) =
      ν.real (Ioi (k - if b then δ / 2 else -(δ / 2))) := by
  rw [locationExperiment_apply, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext x
  simp [sub_lt_iff_lt_add]

theorem hitRate_locationExperiment (k : ℝ) :
    hitRate (locationExperiment ν δ) k = ν.real (Ioi (k - δ / 2)) :=
  locationExperiment_real_Ioi true k

theorem falseAlarmRate_locationExperiment (k : ℝ) :
    falseAlarmRate (locationExperiment ν δ) k = ν.real (Ioi (k + δ / 2)) := by
  rw [falseAlarmRate, locationExperiment_real_Ioi false k]
  simp

/-- In a location experiment the hit rate of `k` is the false-alarm rate of `k - δ`. So on axes
transformed by the inverse of the survival function of `ν`, the receiver operating characteristic
is the chance line shifted by `δ`. -/
theorem hitRate_eq_falseAlarmRate_sub (k : ℝ) :
    hitRate (locationExperiment ν δ) k = falseAlarmRate (locationExperiment ν δ) (k - δ) := by
  rw [hitRate_locationExperiment, falseAlarmRate_locationExperiment]
  ring_nf

section Symmetric

variable [IsProbabilityMeasure ν] [NullSingletonClass ν] [ν.IsNegInvariant]

theorem hitRate_locationExperiment_eq_cdf (k : ℝ) :
    hitRate (locationExperiment ν δ) k = cdf ν (δ / 2 - k) := by
  rw [hitRate_locationExperiment, measureReal_Ioi_eq_cdf_neg ν (measure_singleton _), neg_sub]

theorem falseAlarmRate_locationExperiment_eq_cdf (k : ℝ) :
    falseAlarmRate (locationExperiment ν δ) k = cdf ν (-(δ / 2) - k) := by
  rw [falseAlarmRate_locationExperiment, measureReal_Ioi_eq_cdf_neg ν (measure_singleton _),
    neg_add', neg_sub_comm]

end Symmetric

theorem hitRate_locationExperiment_zero (k : ℝ) :
    hitRate (locationExperiment ν 0) k = falseAlarmRate (locationExperiment ν 0) k := by
  rw [hitRate_eq_falseAlarmRate_sub, sub_zero]

theorem falseAlarmRate_le_hitRate [IsFiniteMeasure ν] (hδ : 0 ≤ δ) (k : ℝ) :
    falseAlarmRate (locationExperiment ν δ) k ≤ hitRate (locationExperiment ν δ) k := by
  rw [hitRate_locationExperiment, falseAlarmRate_locationExperiment]
  exact measureReal_mono (Ioi_subset_Ioi (by linarith))

theorem falseAlarmRate_lt_hitRate [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] (hδ : 0 < δ)
    (k : ℝ) :
    falseAlarmRate (locationExperiment ν δ) k < hitRate (locationExperiment ν δ) k := by
  rw [hitRate_locationExperiment, falseAlarmRate_locationExperiment, ← compl_Iic, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, ← cdf_eq_real, sub_lt_sub_iff_left]
  exact strictMono_cdf ν (by linarith)

end Location

/-! ### The normal model -/

section Normal

variable (δ k : ℝ)

theorem locationExperiment_gaussianReal (b : Bool) :
    locationExperiment (gaussianReal 0 1) δ b =
      gaussianReal (if b then δ / 2 else -(δ / 2)) 1 := by
  rw [locationExperiment_apply, gaussianReal_map_add_const, zero_add]

theorem hitRate_gaussianReal :
    hitRate (locationExperiment (gaussianReal 0 1) δ) k = normalCDF (δ / 2 - k) :=
  hitRate_locationExperiment_eq_cdf k

theorem falseAlarmRate_gaussianReal :
    falseAlarmRate (locationExperiment (gaussianReal 0 1) δ) k = normalCDF (-(δ / 2) - k) :=
  falseAlarmRate_locationExperiment_eq_cdf k

/-- In the normal model the sensitivity is the difference of the z-scores of the rates, whatever the
criterion, so the receiver operating characteristic on z-score axes is the line `z(H) = z(F) + d'`
of unit slope ([macmillan-creelman-2005], eq. (1.8)). -/
theorem probit_hitRate_sub_probit_falseAlarmRate :
    probit (hitRate (locationExperiment (gaussianReal 0 1) δ) k) -
      probit (falseAlarmRate (locationExperiment (gaussianReal 0 1) δ) k) = δ := by
  rw [hitRate_gaussianReal, falseAlarmRate_gaussianReal, probit_normalCDF, probit_normalCDF]
  ring

/-- In the normal model the criterion is minus the mean of the z-scores of the rates,
`c = -(z(H) + z(F)) / 2` ([macmillan-creelman-2005], eq. (2.1)). -/
theorem probit_hitRate_add_probit_falseAlarmRate :
    -(probit (hitRate (locationExperiment (gaussianReal 0 1) δ) k) +
      probit (falseAlarmRate (locationExperiment (gaussianReal 0 1) δ) k)) / 2 = k := by
  rw [hitRate_gaussianReal, falseAlarmRate_gaussianReal, probit_normalCDF, probit_normalCDF]
  ring

/-- In the normal model the likelihood ratio of signal to noise at `x` is `exp (δ * x)`. It is one
midway between the means and increases with `x`. -/
theorem likelihoodRatio_gaussianReal (x : ℝ) :
    gaussianPDFReal (δ / 2) 1 x / gaussianPDFReal (-(δ / 2)) 1 x = Real.exp (δ * x) := by
  rw [gaussianPDFReal_div_gaussianPDFReal _ _ one_ne_zero]
  congr 1
  push_cast
  ring

/-- In the normal model the two-alternative forced choice is the binary probit rule. The difference
of the two observations is `N(δ, 2)`, so the proportion correct is `Φ (δ / √2)`
([macmillan-creelman-2005], eq. (7.6)). -/
theorem forcedChoice_one_gaussianReal :
    forcedChoice (locationExperiment (gaussianReal 0 1) δ) 1 =
      ENNReal.ofReal (normalCDF (δ / √2)) := by
  have h : (fun j : Fin 2 ↦ locationExperiment (gaussianReal 0 1) δ (decide (j = 0))) =
      fun j ↦ gaussianReal (![δ / 2, -(δ / 2)] j) 1 := by
    funext j
    fin_cases j <;> simp [locationExperiment_gaussianReal]
  rw [forcedChoice, h, choiceProb_pi_gaussianReal _ one_ne_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, NNReal.coe_one, mul_one, sub_neg_eq_add,
    add_halves]

end Normal

/-! ### The logistic model -/

section Logistic

variable (δ k : ℝ)

theorem hitRate_logisticMeasure :
    hitRate (locationExperiment logisticMeasure δ) k = Real.sigmoid (δ / 2 - k) := by
  rw [hitRate_locationExperiment_eq_cdf, cdf_logisticMeasure]

theorem falseAlarmRate_logisticMeasure :
    falseAlarmRate (locationExperiment logisticMeasure δ) k = Real.sigmoid (-(δ / 2) - k) := by
  rw [falseAlarmRate_locationExperiment_eq_cdf, cdf_logisticMeasure]

/-- In the logistic model the sensitivity is the difference of the log-odds of the rates for every
criterion, so on log-odds axes the receiver operating characteristic is a line of unit slope, `δ`
above the chance line ([macmillan-creelman-2005], eq. (4.10), with `δ = 2 ln α`). -/
theorem logit_hitRate_sub_logit_falseAlarmRate :
    Real.logit (hitRate (locationExperiment logisticMeasure δ) k) -
      Real.logit (falseAlarmRate (locationExperiment logisticMeasure δ) k) = δ := by
  rw [hitRate_logisticMeasure, falseAlarmRate_logisticMeasure, Real.logit_sigmoid,
    Real.logit_sigmoid]
  ring

/-- In the logistic model the criterion is minus the mean of the log-odds of the rates,
[macmillan-creelman-2005]'s bias `ln b` of eq. (4.12). -/
theorem logit_hitRate_add_logit_falseAlarmRate :
    -(Real.logit (hitRate (locationExperiment logisticMeasure δ) k) +
      Real.logit (falseAlarmRate (locationExperiment logisticMeasure δ) k)) / 2 = k := by
  rw [hitRate_logisticMeasure, falseAlarmRate_logisticMeasure, Real.logit_sigmoid,
    Real.logit_sigmoid]
  ring

end Logistic

end SignalDetection
