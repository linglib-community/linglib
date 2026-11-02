/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Measure
public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.MeasureTheory.Measure.GeomMean

/-!
# Entropy and surprisal

Entropy is [expected surprisal](##measureEntropy_eq_integral_surprisal), and
[the expected surprisal under another measure](##lintegral_surprisal_eq_ofReal_add_klDiv), the
cross-entropy, exceeds it by the Kullback–Leibler divergence. The exponential of minus each is a
geometric mean of masses, of a measure's own masses for
[entropy](##geomMean_eq_exp_neg_measureEntropy) and of the other measure's for
[cross-entropy](##geomMean_eq_exp_neg_lintegral_surprisal).

## References

* [cover-thomas-2006], chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

/-- The geometric mean of the masses of a probability measure under itself is the exponential of
minus its entropy. -/
theorem geomMean_eq_exp_neg_measureEntropy [Fintype S] (μ : Measure S) [IsProbabilityMeasure μ] :
    μ.geomMean (fun s ↦ μ {s}) = ENNReal.ofReal (exp (-Hm[μ])) := by
  rw [Measure.geomMean_eq_ofReal_exp_sum_log (fun _ h ↦ h) fun _ _ ↦ measure_ne_top _ _,
    measureEntropy_eq_sum, ← Finset.sum_neg_distrib]
  simp only [negMulLog, neg_mul, neg_neg, measureReal_def]

/-- Entropy is expected surprisal; an atom of mass zero, whose surprisal is `∞`, contributes `0`
through its real part. -/
theorem measureEntropy_eq_tsum_mul_surprisal (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, μ.real {s} * (surprisal μ s).toReal := by
  simp_rw [measureEntropy_eq_tsum,
    fun s ↦ negMulLog_measureReal_singleton (μ := μ) (s := s) prob_le_one]

theorem measureEntropy_eq_integral_surprisal [Countable S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsZeroOrProbabilityMeasure μ]
    (h : Integrable (fun s ↦ (surprisal μ s).toReal) μ) :
    Hm[μ] = ∫ s, (surprisal μ s).toReal ∂μ := by
  rw [integral_countable h, measureEntropy_eq_tsum_mul_surprisal]
  rfl

variable [MeasurableSingletonClass S]

omit [MeasurableSingletonClass S] in
private theorem surprisal_mul_measure_singleton {ν : Measure S} {s : S} [IsFiniteMeasure μ]
    (hν : ν {s} ≤ 1) (h : μ {s} ≠ 0 → ν {s} ≠ 0) :
    surprisal ν s * μ {s} = ENNReal.ofReal (μ.real {s} * -log (ν.real {s})) := by
  rcases eq_or_ne (μ {s}) 0 with h₀ | h₀
  · simp [h₀, measureReal_def]
  · rw [← ENNReal.ofReal_toReal (surprisal_ne_top_iff.2 (h h₀)),
      ← ENNReal.ofReal_toReal (measure_ne_top μ {s}), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      toReal_surprisal hν, ← measureReal_def, mul_comm]

/-- The cross-entropy, the expected surprisal under `μ` of the atoms as `ν` weighs them, is the
entropy of `μ` plus the divergence of `μ` from `ν`; both sides are infinite unless `μ ≪ ν`. -/
theorem lintegral_surprisal_eq_ofReal_add_klDiv [Fintype S] {ν : Measure S}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫⁻ s, surprisal ν s ∂μ = ENNReal.ofReal (Hm[μ]) + klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  · rw [lintegral_fintype, Finset.sum_congr rfl fun s _ ↦
        surprisal_mul_measure_singleton prob_le_one fun h h0 ↦ h (hμν h0),
      ← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ mul_nonneg measureReal_nonneg
        (neg_nonneg.2 (log_nonpos measureReal_nonneg measureReal_le_one)),
      ← ENNReal.ofReal_toReal (klDiv_ne_top hμν .of_finite),
      ← ENNReal.ofReal_add (measureEntropy_nonneg μ) ENNReal.toReal_nonneg, add_comm,
      toReal_klDiv_add_measureEntropy hμν, ← Finset.sum_neg_distrib]
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun s _ ↦ by ring)
  · rw [klDiv_of_not_ac hμν, add_top, eq_top_iff]
    obtain ⟨s, hμs, hνs⟩ : ∃ s, μ {s} ≠ 0 ∧ ν {s} = 0 := by
      by_contra! h
      exact hμν fun t ht ↦ (measure_null_iff_singleton t.to_countable).2 fun s hs ↦
        not_not.1 fun hμ ↦ h s hμ (measure_mono_null (Set.singleton_subset_iff.2 hs) ht)
    calc ∞ = surprisal ν s * μ {s} := by rw [surprisal_eq_top_iff.2 hνs, ENNReal.top_mul hμs]
      _ ≤ ∫⁻ s, surprisal ν s ∂μ := by
        rw [lintegral_fintype]
        exact Finset.single_le_sum (f := fun s ↦ surprisal ν s * μ {s}) (fun _ _ ↦ zero_le)
          (Finset.mem_univ s)

/-- The geometric mean under `μ` of the masses of a probability measure `ν` is the exponential of
minus the cross-entropy, the expected surprisal under `μ` of the atoms as `ν` weighs them. -/
theorem geomMean_eq_exp_neg_lintegral_surprisal [Fintype S] (μ ν : Measure S) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] :
    (μ.geomMean fun s ↦ ν {s}) = EReal.exp (-((∫⁻ s, surprisal ν s ∂μ : ℝ≥0∞) : EReal)) := by
  rw [← Measure.geomMean_exp_neg]
  exact congrArg _ (funext fun s ↦ (exp_neg_surprisal prob_le_one).symm)

end InformationTheory
