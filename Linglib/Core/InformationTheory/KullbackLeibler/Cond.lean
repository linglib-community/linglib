/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback-Leibler divergence of conditional measures

The conditioning identity: for a probability measure `μ` and an event `s` of nonzero mass,
`klDiv μ[|s] μ = −log μ(s)`, so Bayesian update by pure restriction costs exactly the
information content of the event. More generally the divergence between two conditionings of one
finite measure is the log of the ratio of the events' masses when the first event is almost
contained in the second (`klDiv_cond_cond`), and infinite otherwise
(`klDiv_cond_cond_eq_top_iff`).

`[UPSTREAM]` candidate for `Mathlib/InformationTheory/KullbackLeibler/`
(placement and namespace mirror `ChainRule.lean`, the directory's other
file combining `klDiv` with probability constructions).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

theorem klDiv_cond_self {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) (hs0 : μ s ≠ 0) :
    klDiv μ[|s] μ = ENNReal.ofReal (-Real.log (μ.real s)) := by
  have := cond_isProbabilityMeasure (μ := μ) hs0
  have h : llr μ[|s] μ =ᵐ[μ[|s]] fun _ ↦ -Real.log (μ.real s) := by
    filter_upwards [cond_absolutelyContinuous.ae_le (Measure.rnDeriv_smul_left_of_ne_top'
      (μ.restrict s) μ (ENNReal.inv_ne_top.2 hs0)),
      cond_absolutelyContinuous.ae_le (Measure.rnDeriv_restrict_self μ hs), ae_cond_mem hs]
      with x h₁ h₂ hx
    rw [llr, ProbabilityTheory.cond, h₁, Pi.smul_apply, h₂, Set.indicator_of_mem hx,
      Pi.one_apply, smul_eq_mul, mul_one, ENNReal.toReal_inv, Real.log_inv, measureReal_def]
  rw [klDiv_of_ac_of_integrable cond_absolutelyContinuous ((integrable_const _).congr h.symm),
    integral_congr_ae h]
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {s t : Set Ω}

theorem klDiv_cond_cond (hs : MeasurableSet s) (ht : MeasurableSet t) (hs0 : μ s ≠ 0)
    (hst : s ≤ᵐ[μ] t) :
    klDiv μ[|s] μ[|t] = ENNReal.ofReal (Real.log (μ.real t / μ.real s)) := by
  have hts : μ[|t] s = (μ t)⁻¹ * μ s := by
    rw [cond_apply ht, Set.inter_comm, measure_congr (Filter.inter_eventuallyEqSet_left.2 hst)]
  have := cond_isProbabilityMeasure (μ := μ) fun h ↦ hs0 (measure_mono_null_ae hst h)
  rw [← cond_cond_of_ae_le hs ht hst, klDiv_cond_self _ hs (hts ▸ mul_ne_zero
    (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hs0), measureReal_def μ[|t], hts,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, inv_mul_eq_div,
    ← Real.log_inv, inv_div]

theorem klDiv_cond_cond_lt_iff {t' : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht' : MeasurableSet t') (hs0 : μ s ≠ 0) (hst : s ≤ᵐ[μ] t) (hst' : s ≤ᵐ[μ] t') :
    klDiv μ[|s] μ[|t] < klDiv μ[|s] μ[|t'] ↔ μ t < μ t' := by
  have hpos : 0 < μ.real s := ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  have hle {v : Set Ω} (hv : s ≤ᵐ[μ] v) : μ.real s ≤ μ.real v :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hv)
  rw [klDiv_cond_cond hs ht hs0 hst, klDiv_cond_cond hs ht' hs0 hst',
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.log_nonneg ((one_le_div hpos).2 (hle hst))),
    Real.log_lt_log_iff (div_pos (hpos.trans_le (hle hst)) hpos)
      (div_pos (hpos.trans_le (hle hst')) hpos),
    div_lt_div_iff_of_pos_right hpos, measureReal_def, measureReal_def,
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)]

theorem klDiv_cond_cond_eq_top_iff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    klDiv μ[|s] μ[|t] = ∞ ↔ ¬ s ≤ᵐ[μ] t := by
  refine ⟨fun h hst ↦ ?_, fun h ↦
    klDiv_of_not_ac fun hac ↦ h ((cond_absolutelyContinuous_cond_iff hs ht).1 hac)⟩
  rcases eq_or_ne (μ s) 0 with hs0 | hs0
  · rw [cond_eq_zero_of_meas_eq_zero hs0, klDiv_zero_left] at h
    exact measure_ne_top _ _ h
  · rw [klDiv_cond_cond hs ht hs0 hst] at h
    exact ENNReal.ofReal_ne_top h

end InformationTheory
