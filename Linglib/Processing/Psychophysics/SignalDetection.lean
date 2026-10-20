module

public import Linglib.Core.Probability.Choice.RandomUtility
public import Linglib.Core.Probability.Distributions.Gaussian
public import Linglib.Core.Probability.Distributions.Logistic

/-!
# Signal detection theory

Signal detection theory, in Macmillan and Creelman's presentation, accounts for a yes-no judgment as
a criterion on a noisy decision variable. A trial holds a signal or only noise, the observer
receives an observation whose law depends on which, and it responds "yes" when the observation
exceeds a criterion `k`. The experiment is a kernel `P : Kernel Bool ℝ` from the state of the trial
to the law of the observation, and the observer's response rates are the masses its two laws give to
`(k, ∞)`: the hit rate on signal trials and the false-alarm rate on noise trials. In a forced-choice
task one interval holds the signal and the rest noise, and the observer picks the interval with the
largest observation, so the proportion correct is the choice probability of the signal interval in
the random utility model of the intervals' laws (`forcedChoice`). It is the probability that every
noise observation falls below the signal observation, which for two intervals is the area under the
yes-no receiver operating characteristic, Green and Swets's area theorem
(`forcedChoice_eq_lintegral`).

The models Macmillan and Creelman compare are location experiments (`locationExperiment`): a noise
law `ν` shifted by `δ / 2` on signal trials and by `-(δ / 2)` on noise trials, the sensitivity `δ`
being the distance between the two laws. The normal model takes `ν` standard normal, and Luce's
Choice Theory takes it logistic (Macmillan and Creelman, ch. 4, p. 98). In every location experiment
the hit rate of a criterion is the false-alarm rate of the criterion lower by `δ`
(`hitRate_eq_falseAlarmRate_sub`). For a `ν` without atoms that is symmetric about `0`, such as both
of these, the two rates are the distribution function of `ν` at `δ / 2 - k` and at `-(δ / 2) - k`
(`hitRate_locationExperiment_eq_cdf`, `falseAlarmRate_locationExperiment_eq_cdf`), so the receiver
operating characteristic on axes transformed by the quantile function of `ν` is a line of unit
slope, `δ` above the chance line. In the normal model the axes are z-scores: whatever the criterion
`k`, the sensitivity is `d' = z(H) - z(F)` and `k = -(z(H) + z(F)) / 2`
(`probit_hitRate_sub_probit_falseAlarmRate`, `probit_hitRate_add_probit_falseAlarmRate`). The
likelihood ratio of signal to noise at an observation `x` is `exp (d' * x)`
(`likelihoodRatio_gaussianReal`), and the two-alternative forced choice is the binary probit rule,
with proportion correct `Φ (d' / √2)` (`forcedChoice_one_gaussianReal`).

## Main definitions

* `SignalDetection.hitRate`, `SignalDetection.falseAlarmRate`: the response rates of a criterion.
* `SignalDetection.forcedChoice`: the proportion correct of a forced-choice task.
* `SignalDetection.locationExperiment`: the experiment of a noise law at a sensitivity.

## Main results

* `SignalDetection.forcedChoice_eq_lintegral`: the forced-choice proportion correct as an integral
  over the signal observation, Green and Swets's eq. (2.13).
* `SignalDetection.hitRate_eq_falseAlarmRate_sub`: in a location experiment the hit rate of `k` is
  the false-alarm rate of `k - δ`.
* `SignalDetection.hitRate_locationExperiment_eq_cdf`,
  `SignalDetection.falseAlarmRate_locationExperiment_eq_cdf`: for a noise law without atoms that
  is symmetric about `0`, the rates are its distribution function at `δ / 2 - k` and `-(δ / 2) - k`.
* `SignalDetection.falseAlarmRate_lt_hitRate`: at positive sensitivity the receiver operating
  characteristic lies above the chance line.
* `SignalDetection.probit_hitRate_sub_probit_falseAlarmRate`: in the normal model
  `z(H) = z(F) + d'`, Macmillan and Creelman's eq. (1.8).
* `SignalDetection.probit_hitRate_add_probit_falseAlarmRate`: in the normal model the criterion is
  `c = -(z(H) + z(F)) / 2`, Macmillan and Creelman's eq. (2.1).
* `SignalDetection.likelihoodRatio_gaussianReal`: the likelihood ratio of the normal model.
* `SignalDetection.forcedChoice_one_gaussianReal`: in the normal model the two-alternative
  proportion correct is `Φ (d' / √2)`, Macmillan and Creelman's eq. (7.6).
* `SignalDetection.logit_hitRate_sub_logit_falseAlarmRate`,
  `SignalDetection.logit_hitRate_add_logit_falseAlarmRate`: in the logistic model the
  sensitivity and the criterion are the difference and minus the mean of the log-odds of the rates,
  Macmillan and Creelman's eqs. (4.10) and (4.12).

## Implementation notes

The forced-choice observer picks the interval with the largest observation, where
Green and Swets (p. 46) pick the interval with the largest likelihood ratio. The two rules agree
whenever the likelihood ratio increases with the observation, as it does in the normal model
(`likelihoodRatio_gaussianReal`). Page numbers of Green and Swets are those of the 1988
reprint.

## TODO

* The slope of the receiver operating characteristic at a criterion is the likelihood ratio there
  (Macmillan and Creelman, ch. 2); for the normal model this needs the derivative of `Φ`.
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

/-- The hit rate of the criterion `k`: the probability that the observation on a signal trial
exceeds `k`, so that the observer responds "yes". -/
noncomputable def hitRate : ℝ := (P true).real (Ioi k)

/-- The false-alarm rate of the criterion `k`: the probability that the observation on a noise
trial exceeds `k`. -/
noncomputable def falseAlarmRate : ℝ := (P false).real (Ioi k)

/-- The proportion correct of the forced-choice task with one signal interval and `n` noise
intervals, in which the observer picks the interval with the largest observation: the choice
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

/-- The location experiment of a noise law `ν` at sensitivity `δ`: the observation is `ν` shifted
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

/-- In a location experiment the hit rate of a criterion is the false-alarm rate of the criterion
lower by the sensitivity, so that on axes transformed by the inverse of the survival function of
`ν` the receiver operating characteristic is the chance line shifted by `δ`. -/
theorem hitRate_eq_falseAlarmRate_sub (k : ℝ) :
    hitRate (locationExperiment ν δ) k = falseAlarmRate (locationExperiment ν δ) (k - δ) := by
  rw [hitRate_locationExperiment, falseAlarmRate_locationExperiment]
  ring_nf

section Symmetric

variable [IsProbabilityMeasure ν] [NullSingletonClass ν] [ν.IsNegInvariant]

/-- For a noise law without atoms that is symmetric about `0`, the hit rate of `k` is the
distribution function of `ν` at `δ / 2 - k`. -/
theorem hitRate_locationExperiment_eq_cdf (k : ℝ) :
    hitRate (locationExperiment ν δ) k = cdf ν (δ / 2 - k) := by
  rw [hitRate_locationExperiment, measureReal_Ioi_eq_cdf_neg ν (measure_singleton _), neg_sub]

/-- For a noise law without atoms that is symmetric about `0`, the false-alarm rate of `k` is the
distribution function of `ν` at `-(δ / 2) - k`. -/
theorem falseAlarmRate_locationExperiment_eq_cdf (k : ℝ) :
    falseAlarmRate (locationExperiment ν δ) k = cdf ν (-(δ / 2) - k) := by
  rw [falseAlarmRate_locationExperiment, measureReal_Ioi_eq_cdf_neg ν (measure_singleton _),
    neg_add', neg_sub_comm]

end Symmetric

/-- At zero sensitivity the hit rate is the false-alarm rate: the receiver operating
characteristic is the chance line. -/
theorem hitRate_locationExperiment_zero (k : ℝ) :
    hitRate (locationExperiment ν 0) k = falseAlarmRate (locationExperiment ν 0) k := by
  rw [hitRate_eq_falseAlarmRate_sub, sub_zero]

/-- At nonnegative sensitivity the false-alarm rate is at most the hit rate. -/
theorem falseAlarmRate_le_hitRate [IsFiniteMeasure ν] (hδ : 0 ≤ δ) (k : ℝ) :
    falseAlarmRate (locationExperiment ν δ) k ≤ hitRate (locationExperiment ν δ) k := by
  rw [hitRate_locationExperiment, falseAlarmRate_locationExperiment]
  exact measureReal_mono (Ioi_subset_Ioi (by linarith))

/-- At positive sensitivity the false-alarm rate is below the hit rate when `ν` charges every
nonempty open set: the receiver operating characteristic lies above the chance line. -/
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

/-- In the normal model the observation is `N(δ / 2, 1)` on signal trials and `N(-(δ / 2), 1)` on
noise trials. -/
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

/-- In the normal model the sensitivity is the difference of the z-scores of the rates, whatever
the criterion: the receiver operating characteristic on z-score axes is the line
`z(H) = z(F) + d'` of unit slope ([macmillan-creelman-2005], eq. (1.8)). -/
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

/-- In the normal model the likelihood ratio of signal to noise at an observation `x`, the ratio of
the two densities there, is `exp (δ * x)`: it is one midway between the means and increases with
the observation. -/
theorem likelihoodRatio_gaussianReal (x : ℝ) :
    gaussianPDFReal (δ / 2) 1 x / gaussianPDFReal (-(δ / 2)) 1 x = Real.exp (δ * x) := by
  rw [gaussianPDFReal_div_gaussianPDFReal _ _ one_ne_zero]
  congr 1
  push_cast
  ring

/-- In the normal model the two-alternative forced choice is the binary probit rule: the
difference of the two observations is `N(δ, 2)`, so the proportion correct is `Φ (δ / √2)`
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

/-- In the logistic model the sensitivity is the difference of the log-odds of the rates, whatever
the criterion: on log-odds axes the receiver operating characteristic is a line of unit slope, `δ`
above the chance line, [macmillan-creelman-2005]'s eq. (4.10) with `δ = 2 ln α`. -/
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
