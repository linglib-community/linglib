module

public import Linglib.Core.Probability.Choice.RandomUtility

/-!
# Macmillan and Creelman (2005): Detection Theory: A User's Guide

In a yes-no detection experiment a trial holds a signal or only noise, and the observer says "yes"
when an internal observation exceeds a criterion `k`. The observation has a law `ν` on noise trials
and the translate of `ν` by the sensitivity `d` on signal trials, so the false-alarm rate is
`ν (Ioi k)` and the hit rate is `(ν.map (· + d)) (Ioi k)`. When `ν` is symmetric, [the two rates
differ by `d` on the quantile axes of
`ν`](##MacmillanCreelman2005.quantile_hit_sub_quantile_falseAlarm), whatever the criterion, so that
on those axes the receiver operating characteristic is a line of unit slope. Signal detection theory takes `ν` standard normal, where the quantile is the z-score,
and the Choice Theory of [luce-1959] takes it logistic, where it is [the
log-odds](##MacmillanCreelman2005.logit_hit_sub_logit_falseAlarm). In a forced-choice task the
proportion correct is [the probability that every noise observation falls below the signal
observation](##MacmillanCreelman2005.forcedChoice_eq_lintegral), the area theorem of
[green-swets-1966], and with two intervals and normal noise it is
[`Φ (d / √2)`](##MacmillanCreelman2005.forcedChoice_gaussianReal).

## Implementation notes

* The noise law sits at `0` and the signal law at `d`, where the book puts them at `-d' / 2` and
  `d' / 2` and measures the criterion `c` from their midpoint, so that `c` is `k - d / 2`. The
  sensitivity `ln α` of Choice Theory is `d / 2`.
* The forced-choice observer picks the interval with the largest observation, where
  [green-swets-1966] pick the one with the largest likelihood ratio; the two agree when the
  likelihood ratio increases with the observation, as it does in the normal model.
* Page numbers of [green-swets-1966] are those of the 1988 reprint.

## TODO

* The slope of the receiver operating characteristic at a criterion is the likelihood ratio there;
  for the normal model this needs the derivative of `Φ`.
* The optimal criterion is the Bayes estimator of the experiment under 0-1 loss, and a larger
  sensitivity gives a more informative experiment in the order of
  `Linglib/Core/Probability/Decision/Blackwell.lean`.

## References

* [macmillan-creelman-2005]
* [green-swets-1966]
* [luce-1959]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace MacmillanCreelman2005

/-! ### Yes-no experiments with a translated noise law -/

section Location

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] (d k : ℝ)

theorem falseAlarm_lt_hit {d : ℝ} (hd : 0 < d) :
    ν.real (Ioi k) < (ν.map (· + d)).real (Ioi k) := by
  rw [map_measureReal_apply (measurable_add_const d) measurableSet_Ioi,
    show (· + d) ⁻¹' Ioi k = Ioi (k - d) by ext; simp [sub_lt_iff_lt_add], ← compl_Iic,
    ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, ← cdf_eq_real,
    sub_lt_sub_iff_left]
  exact strictMono_cdf ν (by linarith)

variable [NullSingletonClass ν] [ν.IsNegInvariant]

/-- With a symmetric noise law the sensitivity is the difference of the hit rate and the
false-alarm rate on the quantile axes of the noise law, whatever the criterion. On those axes the
receiver operating characteristic is a line of unit slope, `d` above the chance line. -/
theorem quantile_hit_sub_quantile_falseAlarm :
    quantile ν ((ν.map (· + d)).real (Ioi k)) - quantile ν (ν.real (Ioi k)) = d := by
  rw [measureReal_map_add_const_Ioi_eq_cdf ν d (measure_singleton _),
    measureReal_Ioi_eq_cdf_neg ν (measure_singleton k), quantile_cdf, quantile_cdf]
  ring

theorem quantile_hit_add_quantile_falseAlarm :
    -(quantile ν ((ν.map (· + d)).real (Ioi k)) + quantile ν (ν.real (Ioi k))) / 2 = k - d / 2 := by
  rw [measureReal_map_add_const_Ioi_eq_cdf ν d (measure_singleton _),
    measureReal_Ioi_eq_cdf_neg ν (measure_singleton k), quantile_cdf, quantile_cdf]
  ring

end Location

variable (d k : ℝ)

/-! ### The normal model -/

-- eq. (1.8), p. 11: `z(H) = z(F) + d'`
theorem probit_hit_sub_probit_falseAlarm :
    probit ((gaussianReal d 1).real (Ioi k)) - probit ((gaussianReal 0 1).real (Ioi k)) = d := by
  have h := quantile_hit_sub_quantile_falseAlarm (gaussianReal 0 1) d k
  rwa [gaussianReal_map_add_const, zero_add] at h

-- eq. (2.1), p. 29: `c = -(z(H) + z(F)) / 2`
theorem probit_hit_add_probit_falseAlarm :
    -(probit ((gaussianReal d 1).real (Ioi k)) + probit ((gaussianReal 0 1).real (Ioi k))) / 2 =
      k - d / 2 := by
  have h := quantile_hit_add_quantile_falseAlarm (gaussianReal 0 1) d k
  rwa [gaussianReal_map_add_const, zero_add] at h

/-- In the normal model the likelihood ratio of signal to noise at `x` is `exp (d * (x - d / 2))`.
It is one midway between the means and increases with `x`. -/
theorem likelihoodRatio_gaussianReal (x : ℝ) :
    gaussianPDFReal d 1 x / gaussianPDFReal 0 1 x = exp (d * (x - d / 2)) := by
  rw [gaussianPDFReal_div_gaussianPDFReal _ _ one_ne_zero]
  congr 1
  push_cast
  ring

/-! ### Choice Theory: the logistic model -/

/-- In the logistic model the hit rate and the false-alarm rate differ by the sensitivity on
log-odds axes, for every criterion (eq. (4.10), p. 96, with `d = 2 ln α`). -/
theorem logit_hit_sub_logit_falseAlarm :
    logit ((logisticMeasure.map (· + d)).real (Ioi k)) - logit (logisticMeasure.real (Ioi k)) =
      d := by
  rw [measureReal_map_add_const_Ioi_eq_cdf _ d (measure_singleton _),
    measureReal_Ioi_eq_cdf_neg _ (measure_singleton k), cdf_logisticMeasure_eq,
    cdf_logisticMeasure_eq, logit_sigmoid, logit_sigmoid]
  ring

-- eq. (4.12), p. 97: `ln b = -(ln (H / (1 - H)) + ln (F / (1 - F))) / 2`
theorem logit_hit_add_logit_falseAlarm :
    -(logit ((logisticMeasure.map (· + d)).real (Ioi k)) +
      logit (logisticMeasure.real (Ioi k))) / 2 = k - d / 2 := by
  rw [measureReal_map_add_const_Ioi_eq_cdf _ d (measure_singleton _),
    measureReal_Ioi_eq_cdf_neg _ (measure_singleton k), cdf_logisticMeasure_eq,
    cdf_logisticMeasure_eq, logit_sigmoid, logit_sigmoid]
  ring

/-! ### Forced choice -/

/-- The proportion correct in a forced-choice task with one signal interval and `n` noise
intervals is the probability that all `n` noise observations fall below the signal observation
`k`, integrated over `k` ([green-swets-1966], eqs. (2.7) and (2.13), p. 47). With one noise
interval it is the area under the yes-no receiver operating characteristic. -/
theorem forcedChoice_eq_lintegral (μs μn : Measure ℝ) [SigmaFinite μs] [SigmaFinite μn] (n : ℕ) :
    choiceProb (Measure.pi fun j : Fin (n + 1) ↦ if j = 0 then μs else μn) 0 =
      ∫⁻ k, μn (Iio k) ^ n ∂μs := by
  have : ∀ j : Fin (n + 1), SigmaFinite (if j = 0 then μs else μn) := fun j ↦ by
    split_ifs <;> infer_instance
  rw [choiceProb_pi_eq_lintegral, ite_eq_left rfl]
  refine lintegral_congr fun k ↦ ?_
  rw [Finset.prod_congr rfl fun j hj ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hj)],
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]

/-- In the normal model the proportion correct in two-alternative forced choice is `Φ (d / √2)`,
since the difference of the two observations is normal with mean `d` and variance `2`
(eq. (7.6), p. 172). -/
theorem forcedChoice_gaussianReal :
    choiceProb (Measure.pi fun j : Fin 2 ↦ gaussianReal (![d, 0] j) 1) 0 =
      ENNReal.ofReal (normalCDF (d / √2)) := by
  rw [choiceProb_pi_gaussianReal _ one_ne_zero]
  simp

end MacmillanCreelman2005
