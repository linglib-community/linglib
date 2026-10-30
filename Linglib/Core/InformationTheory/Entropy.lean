/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Probability.IdentDistrib
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Entropy of a measure

This file defines the Shannon entropy of a measure on a measurable space, following the PFR
project's `ForMathlib` entropy, `Hm[μ] = ∑' s, negMulLog (((μ univ)⁻¹ • μ).real {s})`,
normalized so that a finite measure has the entropy of its probability normalization. Mutual
information is the entropy difference `Im[μ] = Hm[μ.fst] + Hm[μ.snd] - Hm[μ]`; on a finite
type it is the real part of the Kullback–Leibler divergence of the joint from the product of its
marginals, hence nonnegative.

Random variables carry the same quantities through their laws: `H[X ; μ] = Hm[μ.map X]`,
the conditional entropy `H[X | Y ; μ]` as the expected entropy of `X` under `Y = y`, and
`I[X : Y ; μ]`; on finite types the chain rule `H[X, Y] = H[Y] + H[X | Y]` holds, conditioning
reduces entropy, conditioning on a function of `Y` leaves at least the entropy that
conditioning on `Y` does, and conditional entropy is the expected conditional surprisal.
Entropies are invariant under injective recodings and depend only on laws. Entropy is the expected
surprisal of a measure under itself, and under another measure the expected surprisal exceeds it by
the Kullback–Leibler divergence.

## Main definitions

* `measureEntropy`, notation `Hm[μ]`; `measureMutualInfo`, notation `Im[μ]`
* `entropy`, notation `H[X ; μ]`; `condEntropy`, notation `H[X | Y ; μ]`;
  `mutualInfo`, notation `I[X : Y ; μ]`

## Main results

* `measureEntropy_le_log_card`: entropy is at most the log of the cardinality, which the uniform
  measure attains.
* `measureMutualInfo_eq_toReal_klDiv`: on a finite product, mutual information is the divergence
  of the joint from the product of its marginals.
* `lintegral_surprisal_eq_ofReal_add_klDiv`: on a finite type, the expected surprisal under `ν` of
  the atoms of `μ` is the entropy of `μ` plus the divergence of `μ` from `ν` (Gibbs' inequality).
* `chain_rule`: `H[X, Y] = H[Y] + H[X | Y]`.
* `mutualInfo_eq_zero_iff`: mutual information vanishes exactly on independent random variables.

## References

* [cover-thomas-2006], chapter 2.
* The PFR project, `PFR/ForMathlib/Entropy/Measure.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

section measureEntropy

variable {μ : Measure S}

/-- Entropy of a measure. The measure is normalized by `(μ Set.univ)⁻¹`, so that a finite
measure has the entropy of its probability normalization and every other measure has entropy
`0`; on a probability measure `simp` removes the normalization. -/
noncomputable def measureEntropy (μ : Measure S) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] scoped notation:100 "Hm[" μ "]" => measureEntropy μ

@[simp] theorem measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

theorem measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

theorem measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _ <;> simp [measureEntropy]

theorem measureEntropy_eq_sum [Fintype S] (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ.real {s}) := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_fintype]

/-- The entropy of a probability measure carried by a finite set is a sum over that set. -/
theorem measureEntropy_of_isProbabilityMeasure_finite {A : Finset S} (hA : μ (↑A)ᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] : Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_of_isProbabilityMeasure, tsum_eq_sum fun s hs ↦ ?_]
  rw [measureReal_def, measure_mono_null (by simpa using hs) hA, ENNReal.toReal_zero,
    negMulLog_zero]

/-- Entropy is expected surprisal; an atom of mass zero, whose surprisal is `∞`, contributes `0`
through its real part. -/
theorem measureEntropy_eq_tsum_mul_surprisal (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, μ.real {s} * (surprisal μ s).toReal := by
  simp_rw [measureEntropy_of_isProbabilityMeasure,
    fun s ↦ negMulLog_measureReal_singleton (μ := μ) (s := s) prob_le_one]

theorem measureEntropy_eq_integral_surprisal [Countable S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsZeroOrProbabilityMeasure μ]
    (h : Integrable (fun s ↦ (surprisal μ s).toReal) μ) :
    Hm[μ] = ∫ s, (surprisal μ s).toReal ∂μ := by
  rw [integral_countable h, measureEntropy_eq_tsum_mul_surprisal]
  rfl

theorem measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simp
    · simp [measureEntropy]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    rw [not_isFiniteMeasure_iff] at hμ
    simp [hμ]

theorem measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ : IsFiniteMeasure μ
  · refine tsum_nonneg fun s ↦ negMulLog_nonneg (by positivity) ?_
    rcases eq_zero_or_neZero μ with rfl | _
    · simp
    · exact measureReal_le_one
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]

/-- Entropy is invariant under an injective recoding of the outcomes. -/
theorem measureEntropy_map_of_injective {U : Type*} [MeasurableSpace U]
    [MeasurableSingletonClass U] {f : S → U} (hf : Measurable f) (hinj : f.Injective) :
    Hm[μ.map f] = Hm[μ] := by
  have hsupp : (Function.support fun u ↦ negMulLog ((((μ.map f) Set.univ)⁻¹ • μ.map f).real {u}))
      ⊆ Set.range f := by
    intro u hu
    by_contra h
    have : f ⁻¹' {u} = ∅ := Set.eq_empty_of_forall_notMem fun s hs ↦ h ⟨s, hs⟩
    simp [measureReal_def, Measure.map_apply hf (.singleton u), this] at hu
  rw [measureEntropy, ← hinj.tsum_eq hsupp, measureEntropy, Measure.map_apply hf .univ,
    Set.preimage_univ]
  congr with s
  rw [measureReal_def, measureReal_def, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hf (.singleton _), ← Set.image_singleton, hinj.preimage_image]

variable [MeasurableSingletonClass S]

@[simp] theorem measureEntropy_dirac (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy_of_isProbabilityMeasure_finite (A := {x}) (by simp), Finset.sum_singleton]
  simp

private theorem measureEntropy_le_log_card_of_isProbabilityMeasure [Fintype S] (μ : Measure S)
    [IsProbabilityMeasure μ] : Hm[μ] ≤ log (Fintype.card S) := by
  have : Nonempty S := μ.nonempty_of_neZero
  set N := Fintype.card S
  have hN : (N : ℝ) ≠ 0 := by positivity
  rw [measureEntropy_eq_sum]
  calc ∑ s, negMulLog (μ.real {s}) = N * ∑ s, (N : ℝ)⁻¹ * negMulLog (μ.real {s}) := by
        rw [Finset.mul_sum]
        congr with s
        rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
    _ ≤ N * negMulLog (∑ s, (N : ℝ)⁻¹ * μ.real {s}) := by
        gcongr
        exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [N]) (by simp)
    _ = N * negMulLog (N : ℝ)⁻¹ := by
        rw [← Finset.mul_sum, sum_measureReal_singleton_eq_one, mul_one]
    _ = log N := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ hN]

/-- Entropy is at most the logarithm of the cardinality of the type. -/
theorem measureEntropy_le_log_card [Fintype S] (μ : Measure S) :
    Hm[μ] ≤ log (Fintype.card S) := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simpa using log_natCast_nonneg (Fintype.card S)
    · rw [← measureEntropy_univ_smul]
      exact measureEntropy_le_log_card_of_isProbabilityMeasure _
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    exact log_natCast_nonneg _

/-- The entropy of the uniform measure on a finite set is the logarithm of its cardinality. -/
theorem measureEntropy_uniformOn {A : Finset S} (hA : A.Nonempty) :
    Hm[uniformOn (A : Set S)] = log A.card := by
  classical
  have := isProbabilityMeasure_uniformOn A.finite_toSet (by simpa using hA)
  rw [measureEntropy_of_isProbabilityMeasure_finite (A := A)
      ((uniformOn_eq_zero_iff A.finite_toSet).2 (Set.inter_compl_self _)),
    Finset.sum_congr rfl (g := fun _ ↦ negMulLog (A.card : ℝ)⁻¹) fun s hs ↦ by
      simp [uniformOn_finset_real_singleton, hs],
    Finset.sum_const, nsmul_eq_mul, negMulLog, log_inv]
  field_simp [hA.card_pos.ne']

/-- A probability measure on a finite type has zero entropy iff it is a Dirac mass. -/
theorem measureEntropy_eq_zero_iff [Fintype S] (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = 0 ↔ ∃ x, μ = Measure.dirac x := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ measureEntropy_dirac x⟩
  rw [measureEntropy_eq_sum] at h
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun s _ ↦
    negMulLog_nonneg measureReal_nonneg measureReal_le_one).1 h
  have hmass : ∀ s : S, μ.real {s} = 0 ∨ μ.real {s} = 1 := by
    intro s
    have hs := hzero s (Finset.mem_univ s)
    rw [negMulLog, neg_mul, neg_eq_zero, mul_eq_zero] at hs
    rcases hs with h0 | h0
    · exact .inl h0
    · rcases log_eq_zero.1 h0 with h1 | h1 | h1
      · exact .inl h1
      · exact .inr h1
      · exact absurd (h1 ▸ measureReal_nonneg) (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x : S, μ.real {x} = 1 := by
    by_contra hno
    refine zero_ne_one (α := ℝ) ?_
    rw [← sum_measureReal_singleton_eq_one μ]
    exact (Finset.sum_eq_zero fun s _ ↦
      (hmass s).resolve_right fun h1 ↦ hno ⟨s, h1⟩).symm
  have hμx : μ {x} = 1 := by rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at hx
  refine ⟨x, Measure.ext_iff_singleton.2 fun a ↦ ?_⟩
  rcases eq_or_ne a x with rfl | ha
  · rw [hμx, Measure.dirac_apply_of_mem (Set.mem_singleton a)]
  · rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using ha.symm)]
    exact measure_mono_null (Set.singleton_subset_iff.2 (by simpa using ha))
      ((prob_compl_eq_zero_iff (.singleton x)).2 hμx)

/-- On a finite type the divergence is the textbook relative entropy, the `μ`-expected log-ratio
of the masses of the atoms. -/
theorem toReal_klDiv_eq_sum_log_div [Fintype S] {ν : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ s, μ.real {s} * log (μ.real {s} / ν.real {s}) := by
  have h : llr μ ν =ᵐ[μ] fun s ↦ log (μ.real {s} / ν.real {s}) := by
    refine ae_iff_of_countable.2 fun s hs ↦ ?_
    dsimp only
    have hd := Measure.setLIntegral_rnDeriv hμν {s}
    rw [lintegral_singleton] at hd
    rw [llr, measureReal_def, measureReal_def, ← ENNReal.toReal_div, ← hd,
      ENNReal.mul_div_cancel_right (fun h ↦ hs (hμν h)) (measure_ne_top _ _)]
  rw [toReal_klDiv_of_measure_eq hμν (by simp), integral_congr_ae h, integral_fintype .of_finite]
  simp

/-- The divergence and the entropy add up to the cross-entropy, the expected surprisal under `μ`
of the atoms as `ν` weighs them. -/
theorem toReal_klDiv_add_measureEntropy [Fintype S] {ν : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal + Hm[μ] = -∑ s, μ.real {s} * log (ν.real {s}) := by
  rw [toReal_klDiv_eq_sum_log_div hμν, measureEntropy_eq_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rcases eq_or_ne (μ.real {s}) 0 with h0 | h0
  · simp [h0]
  · rw [log_div h0 fun h ↦ h0 ((measureReal_eq_zero_iff (measure_ne_top _ _)).2
      (hμν ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h))), negMulLog]
    ring

/-- Gibbs' variational identity for a row of a weight kernel. The divergence from the row and the
entropy add up to the log of the total weight less the expected log-weight, so the row is the
distribution with the greatest entropy plus expected log-weight. -/
theorem toReal_klDiv_ofWeights_add_measureEntropy {ι : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [Fintype S] [IsProbabilityMeasure μ] {w : ι → S → ℝ≥0∞} {i : ι}
    (hw : ∀ s, w i s ≠ ∞) (hμ : μ ≪ Kernel.ofWeights w i) :
    (klDiv μ (Kernel.ofWeights w i)).toReal + Hm[μ] =
      log (∑ s, (w i s).toReal) - ∑ s, μ.real {s} * log (w i s).toReal := by
  have := Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous hw hμ
  have hterm (s : S) : μ.real {s} * log ((Kernel.ofWeights w i).real {s}) =
      μ.real {s} * log (w i s).toReal - μ.real {s} * log (∑ s, (w i s).toReal) := by
    rcases eq_or_ne (μ.real {s}) 0 with h | h
    · simp [h]
    · have hp : (Kernel.ofWeights w i).real {s} ≠ 0 := fun h0 ↦
        h ((measureReal_eq_zero_iff (measure_ne_top _ _)).2
          (hμ ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0)))
      rw [Kernel.ofWeights_real_singleton w i hw] at hp ⊢
      rw [log_div (fun h0 ↦ hp (by rw [h0, zero_div])) fun h0 ↦ hp (by rw [h0, div_zero]), mul_sub]
  rw [toReal_klDiv_add_measureEntropy hμ, Finset.sum_congr rfl fun s _ ↦ hterm s,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul, neg_sub]

/-! ### Expected surprisal -/

omit [MeasurableSingletonClass S] in
private theorem surprisal_mul_measure_singleton {ν : Measure S} {s : S} [IsFiniteMeasure μ]
    (hν : ν {s} ≤ 1) (h : μ {s} ≠ 0 → ν {s} ≠ 0) :
    surprisal ν s * μ {s} = ENNReal.ofReal (μ.real {s} * -log (ν.real {s})) := by
  rcases eq_or_ne (μ {s}) 0 with h₀ | h₀
  · simp [h₀, measureReal_def]
  · rw [← ENNReal.ofReal_toReal (surprisal_ne_top_iff.2 (h h₀)),
      ← ENNReal.ofReal_toReal (measure_ne_top μ {s}), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      toReal_surprisal hν, ← measureReal_def, mul_comm]

/-- The expected surprisal of a measure under itself is the sum of the summands of its entropy,
infinite when they are not summable. -/
theorem lintegral_surprisal_self [Countable S] (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    ∫⁻ s, surprisal μ s ∂μ = ∑' s, ENNReal.ofReal (negMulLog (μ.real {s})) := by
  rw [lintegral_countable']
  refine tsum_congr fun s ↦ ?_
  rw [surprisal_mul_measure_singleton prob_le_one id, negMulLog]
  ring_nf

theorem ofReal_measureEntropy [Countable S] (μ : Measure S) [IsZeroOrProbabilityMeasure μ]
    (h : Summable fun s ↦ negMulLog (μ.real {s})) :
    ENNReal.ofReal (Hm[μ]) = ∫⁻ s, surprisal μ s ∂μ := by
  rw [lintegral_surprisal_self, measureEntropy_of_isProbabilityMeasure,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ negMulLog_nonneg measureReal_nonneg measureReal_le_one)
      h]

omit [MeasurableSingletonClass S] in
/-- Expected surprisal is invariant under an injective recoding of the values. -/
theorem lintegral_surprisal_map_of_injective {U : Type*} [MeasurableSpace U] [Countable U]
    [MeasurableSingletonClass U] {f : S → U} (hf : Measurable f) (hinj : f.Injective)
    (μ : Measure S) :
    ∫⁻ u, surprisal (μ.map f) u ∂(μ.map f) = ∫⁻ s, surprisal μ s ∂μ := by
  rw [lintegral_map (measurable_of_countable _) hf]
  simp_rw [surprisal_map_of_injective hf hinj]

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

/-- Gibbs' inequality: the expected surprisal under another measure is at least the entropy. -/
theorem ofReal_measureEntropy_le_lintegral_surprisal [Fintype S] {ν : Measure S}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (Hm[μ]) ≤ ∫⁻ s, surprisal ν s ∂μ := by
  rw [lintegral_surprisal_eq_ofReal_add_klDiv]
  exact le_self_add

/-- The expected surprisal under another measure attains the entropy only at the measure itself. -/
theorem lintegral_surprisal_eq_ofReal_measureEntropy_iff [Fintype S] {ν : Measure S}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫⁻ s, surprisal ν s ∂μ = ENNReal.ofReal (Hm[μ]) ↔ μ = ν := by
  rw [lintegral_surprisal_eq_ofReal_add_klDiv, ← klDiv_eq_zero_iff]
  conv_lhs => rhs; rw [← add_zero (ENNReal.ofReal (Hm[μ]))]
  exact ENNReal.add_right_inj ENNReal.ofReal_ne_top

end measureEntropy

section measureMutualInfo

/-- The mutual information of a measure on a product is the sum of the entropies of its
marginals less the entropy of the joint. -/
noncomputable def measureMutualInfo (μ : Measure (S × T)) : ℝ :=
  Hm[μ.fst] + Hm[μ.snd] - Hm[μ]

@[inherit_doc measureMutualInfo] scoped notation:100 "Im[" μ "]" => measureMutualInfo μ

/-- Mutual information is symmetric in the two coordinates. -/
theorem measureMutualInfo_map_swap [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (ρ : Measure (S × T)) : Im[ρ.map Prod.swap] = Im[ρ] := by
  rw [measureMutualInfo, measureMutualInfo, Measure.fst_map_swap, Measure.snd_map_swap,
    measureEntropy_map_of_injective measurable_swap Prod.swap_injective]
  ring

variable [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  (μ : Measure (S × T)) [IsProbabilityMeasure μ]

/-- On a finite product, mutual information is the real part of the Kullback–Leibler
divergence of the joint from the product of its marginals. -/
theorem measureMutualInfo_eq_toReal_klDiv : Im[μ] = (klDiv μ (μ.fst.prod μ.snd)).toReal := by
  have h (a : S) (b : T) :
      μ.real {(a, b)} * log (μ.real {(a, b)} / (μ.fst.prod μ.snd).real {(a, b)})
        = -negMulLog (μ.real {(a, b)}) - μ.real {(a, b)} * log (μ.fst.real {a})
          - μ.real {(a, b)} * log (μ.snd.real {b}) := by
    rw [Measure.prod_real_singleton]
    obtain hp | hp := eq_or_ne (μ.real {(a, b)}) 0
    · simp [hp]
    · have hpos : 0 < μ.real {(a, b)} := lt_of_le_of_ne measureReal_nonneg hp.symm
      have ha : μ.real {(a, b)} ≤ μ.fst.real {a} := by
        rw [Measure.fst_real_singleton_eq_sum]
        exact Finset.single_le_sum (f := fun b ↦ μ.real {(a, b)}) (fun _ _ ↦ measureReal_nonneg)
          (Finset.mem_univ b)
      have hb : μ.real {(a, b)} ≤ μ.snd.real {b} := by
        rw [Measure.snd_real_singleton_eq_sum]
        exact Finset.single_le_sum (f := fun a ↦ μ.real {(a, b)}) (fun _ _ ↦ measureReal_nonneg)
          (Finset.mem_univ a)
      rw [log_div hp (mul_ne_zero (hpos.trans_le ha).ne' (hpos.trans_le hb).ne'),
        log_mul (hpos.trans_le ha).ne' (hpos.trans_le hb).ne', negMulLog]
      ring
  have h1 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.fst.real {a})
      = ∑ a, μ.fst.real {a} * log (μ.fst.real {a}) := by
    simp_rw [← Finset.sum_mul, ← Measure.fst_real_singleton_eq_sum]
  have h2 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.snd.real {b})
      = ∑ b, μ.snd.real {b} * log (μ.snd.real {b}) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Measure.snd_real_singleton_eq_sum]
  rw [toReal_klDiv_eq_sum_log_div μ.absolutelyContinuous_fst_prod_snd,
    measureMutualInfo, measureEntropy_eq_sum, measureEntropy_eq_sum, measureEntropy_eq_sum]
  simp_rw [Fintype.sum_prod_type, h, Finset.sum_sub_distrib, Finset.sum_neg_distrib, h1, h2,
    negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

theorem measureMutualInfo_nonneg : 0 ≤ Im[μ] := by
  rw [measureMutualInfo_eq_toReal_klDiv]
  exact ENNReal.toReal_nonneg

/-- A product measure carries no mutual information. -/
theorem measureMutualInfo_prod (ν₁ : Measure S) (ν₂ : Measure T) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] : Im[ν₁.prod ν₂] = 0 := by
  rw [measureMutualInfo_eq_toReal_klDiv, Measure.fst_prod, Measure.snd_prod, klDiv_self,
    ENNReal.toReal_zero]

/-- **Data processing.** Pushing the second coordinate through a Markov kernel cannot increase
mutual information. -/
theorem measureMutualInfo_parallelComp_id_comp_le {U : Type*} [MeasurableSpace U] [Fintype U]
    [MeasurableSingletonClass U] (η : Kernel T U) [IsMarkovKernel η] :
    Im[(Kernel.id ∥ₖ η) ∘ₘ μ] ≤ Im[μ] := by
  have : Nonempty T := μ.nonempty_of_neZero.map Prod.snd
  rw [measureMutualInfo_eq_toReal_klDiv, measureMutualInfo_eq_toReal_klDiv,
    Measure.fst_parallelComp_id_comp, Measure.snd_parallelComp_id_comp,
    Measure.prod_comp_right]
  exact ENNReal.toReal_mono
    (klDiv_ne_top_iff.mpr ⟨μ.absolutelyContinuous_fst_prod_snd, .of_finite⟩)
    (klDiv_comp_right_le _ _ _)

end measureMutualInfo

section entropy

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → S} {Y : Ω → T}

/-- The entropy of a random variable is the entropy of its law. -/
noncomputable def entropy (X : Ω → S) (μ : Measure Ω) : ℝ := Hm[μ.map X]

@[inherit_doc entropy] scoped notation3:max "H[" X " ; " μ "]" => entropy X μ

theorem entropy_def (X : Ω → S) (μ : Measure Ω) : H[X ; μ] = Hm[μ.map X] := rfl

theorem entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ H[X ; μ] := measureEntropy_nonneg _

@[simp] theorem entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by
  simp [entropy]

theorem entropy_le_log_card [Fintype S] [MeasurableSingletonClass S] (X : Ω → S)
    (μ : Measure Ω) : H[X ; μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

theorem entropy_eq_sum [Fintype S] [MeasurableSingletonClass S] (hX : Measurable X)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    H[X ; μ] = ∑ s, negMulLog (μ.real (X ⁻¹' {s})) := by
  rw [entropy, measureEntropy_eq_sum]
  simp_rw [map_measureReal_apply hX (.singleton _)]

/-- The entropy of a random variable valued in a finite set is a sum over that set. -/
theorem entropy_eq_sum_finset [MeasurableSingletonClass S] (hX : Measurable X) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] {A : Finset S} (hA : ∀ ω, X ω ∈ A) :
    H[X ; μ] = ∑ s ∈ A, negMulLog (μ.real (X ⁻¹' {s})) := by
  rw [entropy, measureEntropy_of_isProbabilityMeasure_finite (A := A)]
  · simp_rw [map_measureReal_apply hX (.singleton _)]
  · rw [Measure.map_apply hX A.measurableSet.compl]
    convert measure_empty (μ := μ)
    ext ω
    simpa using hA ω

/-- A random variable with at most one value has no entropy. -/
theorem entropy_of_subsingleton [Fintype S] [MeasurableSingletonClass S] [Subsingleton S]
    (X : Ω → S) (μ : Measure Ω) : H[X ; μ] = 0 :=
  le_antisymm ((entropy_le_log_card X μ).trans <| log_nonpos (Nat.cast_nonneg _) <|
    Nat.cast_le_one.mpr (Fintype.card_le_one_iff_subsingleton.mpr ‹_›)) (entropy_nonneg X μ)

/-- A constant random variable has no entropy. -/
theorem entropy_const [MeasurableSingletonClass S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : S) : H[fun _ ↦ x ; μ] = 0 := by
  rw [entropy_def, Measure.map_const, measure_univ, one_smul, measureEntropy_dirac]

/-- A random variable has zero entropy iff it is almost surely constant. -/
theorem entropy_eq_zero_iff [Fintype S] [MeasurableSingletonClass S] (hX : Measurable X)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : H[X ; μ] = 0 ↔ ∃ x, ∀ᵐ ω ∂μ, X ω = x := by
  have : IsProbabilityMeasure (μ.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 ‹_›
  rw [entropy_def, measureEntropy_eq_zero_iff]
  refine exists_congr fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h1 : μ (X ⁻¹' {x}) = 1 := by
      have := congrArg (· {x}) h
      simpa [Measure.map_apply hX (.singleton x), Measure.dirac_apply_of_mem] using this
    rw [ae_iff, show {ω | ¬ X ω = x} = (X ⁻¹' {x})ᶜ from rfl,
      prob_compl_eq_zero_iff (hX (.singleton x))]
    exact h1
  · rw [Measure.map_congr (h.mono fun ω hω ↦ hω : X =ᵐ[μ] fun _ ↦ x), Measure.map_const,
      measure_univ, one_smul]

/-- Entropy is invariant under an injective recoding of the values. -/
theorem entropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) {f : S → T} (hf : Measurable f) (hinj : f.Injective) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  rw [entropy_def, ← Measure.map_map hf hX, measureEntropy_map_of_injective hf hinj, entropy_def]

theorem entropy_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T] (μ : Measure Ω)
    (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[fun ω ↦ (Y ω, X ω) ; μ] :=
  (entropy_comp_of_injective μ (hX.prodMk hY) measurable_swap Prod.swap_injective).symm

theorem _root_.ProbabilityTheory.IdentDistrib.entropy_eq {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X' : Ω' → S} (h : IdentDistrib X X' μ ν) :
    H[X ; μ] = H[X' ; ν] := by
  rw [entropy_def, entropy_def, h.map_eq]

/-- The conditional entropy of `X` given `Y` is the expectation, under the law of `Y`, of the
entropy of `X` conditioned on `Y = y`. -/
noncomputable def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  ∫ y, H[X ; μ[|Y ⁻¹' {y}]] ∂(μ.map Y)

@[inherit_doc condEntropy]
scoped notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

theorem condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg fun _ ↦ entropy_nonneg _ _

theorem condEntropy_eq_sum [Fintype T] [MeasurableSingletonClass T] (X : Ω → S)
    (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    H[X | Y ; μ] = ∑ y, μ.real (Y ⁻¹' {y}) * H[X ; μ[|Y ⁻¹' {y}]] := by
  rw [condEntropy, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, map_measureReal_apply hY (.singleton _)]

/-- Recoding `X` injectively leaves its entropy given `Y` unchanged. -/
theorem condEntropy_comp_of_injective [MeasurableSingletonClass S] {U : Type*} [MeasurableSpace U]
    [MeasurableSingletonClass U] (Y : Ω → T) (μ : Measure Ω) (hX : Measurable X) {f : S → U}
    (hf : Measurable f) (hinj : f.Injective) : H[f ∘ X | Y ; μ] = H[X | Y ; μ] := by
  simp only [condEntropy, entropy_comp_of_injective _ hX hf hinj]

/-- Recoding `Y` by a measurable embedding leaves the entropy of `X` given `Y` unchanged. -/
theorem condEntropy_comp_right_of_measurableEmbedding {U : Type*} [MeasurableSpace U]
    (X : Ω → S) (μ : Measure Ω) (hY : Measurable Y) {g : T → U} (hg : MeasurableEmbedding g) :
    H[X | g ∘ Y ; μ] = H[X | Y ; μ] := by
  rw [condEntropy, ← Measure.map_map hg.measurable hY, hg.integral_map, condEntropy]
  congr with y
  rw [Set.preimage_comp, ← Set.image_singleton, hg.injective.preimage_image]

/-- Mutual information of two random variables. -/
noncomputable def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[fun ω ↦ (X ω, Y ω) ; μ]

@[inherit_doc mutualInfo]
scoped notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

theorem mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[fun ω ↦ (X ω, Y ω) ; μ] := rfl

/-- The mutual information of two random variables is that of their joint law. -/
theorem mutualInfo_eq_measureMutualInfo (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) : I[X : Y ; μ] = Im[μ.map fun ω ↦ (X ω, Y ω)] := by
  rw [mutualInfo, measureMutualInfo, Measure.fst_map_prodMk hX hY, Measure.snd_map_prodMk hX hY]
  rfl

/-- Mutual information is symmetric. -/
theorem mutualInfo_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T] (μ : Measure Ω)
    (hX : Measurable X) (hY : Measurable Y) : I[X : Y ; μ] = I[Y : X ; μ] := by
  rw [mutualInfo_def, mutualInfo_def, entropy_comm μ hX hY]
  ring

variable [Fintype S] [Fintype T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) : 0 ≤ I[X : Y ; μ] := by
  have : IsProbabilityMeasure (μ.map fun ω ↦ (X ω, Y ω)) :=
    ⟨by rw [Measure.map_apply (hX.prodMk hY) .univ, Set.preimage_univ, measure_univ]⟩
  rw [mutualInfo_eq_measureMutualInfo hX hY]
  exact measureMutualInfo_nonneg _

/-- **Chain rule.** The entropy of a pair is `H[X, Y] = H[Y] + H[X | Y]`. -/
theorem chain_rule (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  have hfib (x : S) (y : T) :
      Y ⁻¹' {y} ∩ X ⁻¹' {x} = (fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)} := by
    ext ω; simp [and_comm]
  have hcond (x : S) (y : T) : (μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x})
      = μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y}) := by
    rw [measureReal_def, cond_apply (hY (.singleton y)), ENNReal.toReal_mul,
      ENNReal.toReal_inv, hfib, div_eq_inv_mul]
    rfl
  have hsum (y : T) :
      ∑ x, μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) = μ.real (Y ⁻¹' {y}) := by
    simp_rw [← map_measureReal_apply (hX.prodMk hY) (.singleton _),
      ← Measure.snd_real_singleton_eq_sum, Measure.snd_map_prodMk hX hY,
      map_measureReal_apply hY (.singleton _)]
  have key (y : T) : μ.real (Y ⁻¹' {y}) * H[X ; μ[|Y ⁻¹' {y}]]
      = ∑ x, negMulLog (μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}))
        - negMulLog (μ.real (Y ⁻¹' {y})) := by
    obtain hy | hy := eq_or_ne (μ (Y ⁻¹' {y})) 0
    · have h0 (x : S) : μ ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) = 0 :=
        measure_mono_null (hfib x y ▸ Set.inter_subset_left) hy
      simp [cond_eq_zero_of_meas_eq_zero hy, measureReal_def, hy, h0]
    · have := cond_isProbabilityMeasure (μ := μ) hy
      have hq : μ.real (Y ⁻¹' {y}) ≠ 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).not.mpr hy
      have h (x : S) : μ.real (Y ⁻¹' {y})
            * negMulLog (μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y}))
          = negMulLog (μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}))
            - μ.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' {(x, y)}) / μ.real (Y ⁻¹' {y})
              * negMulLog (μ.real (Y ⁻¹' {y})) := by
        rw [eq_sub_iff_add_eq, add_comm, ← negMulLog_mul]
        congr 1
        field_simp
      rw [entropy_eq_sum hX, Finset.mul_sum]
      simp_rw [hcond, h, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hsum,
        div_self hq, one_mul]
  rw [entropy_eq_sum (hX.prodMk hY), entropy_eq_sum hY, condEntropy_eq_sum X hY]
  simp_rw [key, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  ring

theorem mutualInfo_eq_entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo, chain_rule μ hX hY]
  ring

/-- Conditioning reduces entropy, `H[X | Y] ≤ H[X]`. -/
theorem condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.mp (mutualInfo_eq_entropy_sub_condEntropy μ hX hY ▸ mutualInfo_nonneg μ hX hY)

/-- Mutual information vanishes exactly on independent random variables. -/
theorem mutualInfo_eq_zero_iff (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = 0 ↔ X ⟂ᵢ[μ] Y := by
  rw [mutualInfo_eq_measureMutualInfo hX hY, measureMutualInfo_eq_toReal_klDiv,
    ENNReal.toReal_eq_zero_iff, or_iff_left (klDiv_ne_top_iff.mpr
      ⟨(μ.map fun ω ↦ (X ω, Y ω)).absolutelyContinuous_fst_prod_snd, .of_finite⟩),
    klDiv_eq_zero_iff, Measure.fst_map_prodMk hX hY, Measure.snd_map_prodMk hX hY,
    indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

variable {μ} in
/-- The entropy of a pair of independent random variables is the sum of their entropies. -/
theorem _root_.ProbabilityTheory.IndepFun.entropy_pair_eq_add (h : X ⟂ᵢ[μ] Y)
    (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω ↦ (X ω, Y ω) ; μ] = H[X ; μ] + H[Y ; μ] := by
  have := (mutualInfo_eq_zero_iff μ hX hY).mpr h
  rw [mutualInfo_def] at this
  linarith

variable {μ} in
/-- Conditioning on an independent random variable leaves entropy unchanged. -/
theorem _root_.ProbabilityTheory.IndepFun.condEntropy_eq_entropy (h : X ⟂ᵢ[μ] Y)
    (hX : Measurable X) (hY : Measurable Y) : H[X | Y ; μ] = H[X ; μ] := by
  have := (mutualInfo_eq_zero_iff μ hX hY).mpr h
  rw [mutualInfo_eq_entropy_sub_condEntropy μ hX hY] at this
  linarith

/-- Conditioning also on a random variable independent of the pair `(X, Y)` leaves the entropy
of `X` given `Y` unchanged. -/
theorem condEntropy_prod_eq_of_indepFun {U : Type*} [MeasurableSpace U] [Fintype U]
    [MeasurableSingletonClass U] {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (h : (fun ω ↦ (X ω, Y ω)) ⟂ᵢ[μ] Z) :
    H[X | fun ω ↦ (Y ω, Z ω) ; μ] = H[X | Y ; μ] := by
  have e : H[fun ω ↦ ((X ω, Y ω), Z ω) ; μ] = H[fun ω ↦ (X ω, Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (hX.prodMk (hY.prodMk hZ)) (f := (Equiv.prodAssoc S T U).symm)
      (measurable_of_finite _) (Equiv.prodAssoc S T U).symm.injective
  have hYZ : Y ⟂ᵢ[μ] Z := h.comp measurable_snd measurable_id
  linarith [chain_rule μ hX (hY.prodMk hZ), chain_rule μ hX hY,
    h.entropy_pair_eq_add (hX.prodMk hY) hZ, hYZ.entropy_pair_eq_add hY hZ]

section comp

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]

/-- **Data processing.** A function of `Y` carries no more information about `X` than `Y`. -/
theorem mutualInfo_comp_le (hX : Measurable X) (hY : Measurable Y) (f : T → U) :
    I[X : f ∘ Y ; μ] ≤ I[X : Y ; μ] := by
  have hf : Measurable f := measurable_of_finite f
  have h := measureMutualInfo_parallelComp_id_comp_le (μ.map fun ω ↦ (X ω, Y ω))
    (Kernel.deterministic f hf)
  rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (hX.prodMk hY),
    ← mutualInfo_eq_measureMutualInfo hX hY] at h
  rwa [mutualInfo_eq_measureMutualInfo hX (hf.comp hY)]

/-- Conditioning on a function of `Y` leaves at least the entropy that conditioning on `Y`
leaves. -/
theorem condEntropy_le_condEntropy_comp (hX : Measurable X) (hY : Measurable Y) (f : T → U) :
    H[X | Y ; μ] ≤ H[X | f ∘ Y ; μ] := by
  have h := mutualInfo_comp_le μ hX hY f
  rw [mutualInfo_eq_entropy_sub_condEntropy μ hX hY,
    mutualInfo_eq_entropy_sub_condEntropy μ hX ((measurable_of_finite f).comp hY)] at h
  linarith

/-- Recoding `X` injectively, in a way that may depend on `Y`, leaves the entropy of `X` given
`Y` unchanged. -/
theorem condEntropy_of_injective (hX : Measurable X) (hY : Measurable Y) (f : T → S → U)
    (hf : ∀ t, (f t).Injective) : H[fun ω ↦ f (Y ω) (X ω) | Y ; μ] = H[X | Y ; μ] := by
  have hfXY : Measurable fun ω ↦ f (Y ω) (X ω) :=
    (measurable_of_finite (Function.uncurry f)).comp (hY.prodMk hX)
  have he : (fun p : S × T ↦ (f p.2 p.1, p.2)).Injective := fun p q h ↦ by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf p.2 (h.2 ▸ h.1)) h.2
  have h := chain_rule μ hfXY hY
  rw [show (fun ω ↦ (f (Y ω) (X ω), Y ω)) = (fun p : S × T ↦ (f p.2 p.1, p.2)) ∘
    fun ω ↦ (X ω, Y ω) from rfl, entropy_comp_of_injective μ (hX.prodMk hY)
      (measurable_of_finite _) he, chain_rule μ hX hY] at h
  linarith

/-- A function of `Y` has no entropy given `Y`. -/
theorem condEntropy_comp_self (hY : Measurable Y) (f : T → U) : H[f ∘ Y | Y ; μ] = 0 := by
  have h := chain_rule μ ((measurable_of_finite f).comp hY) hY
  rw [show (fun ω ↦ ((f ∘ Y) ω, Y ω)) = (fun t ↦ (f t, t)) ∘ Y from rfl,
    entropy_comp_of_injective μ hY (measurable_of_finite _) fun _ _ h ↦ (Prod.mk.inj h).2] at h
  linarith

/-- A function of a random variable has at most its entropy. -/
theorem entropy_comp_le (hX : Measurable X) (f : S → U) : H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have hf : Measurable (f ∘ X) := (measurable_of_finite f).comp hX
  have h₁ := chain_rule μ hf hX
  have h₂ := chain_rule μ hX hf
  have h₃ := condEntropy_comp_self μ hX f
  have h₄ := entropy_comm μ hf hX
  have h₅ := condEntropy_nonneg X (f ∘ X) μ
  linarith

/-- A random variable has at most the entropy of its sample-space measure. -/
theorem entropy_le_measureEntropy [Fintype Ω] [MeasurableSingletonClass Ω] (X : Ω → S) :
    H[X ; μ] ≤ Hm[μ] := by
  have h := entropy_comp_le (X := id) μ measurable_id X
  rwa [Function.comp_id, entropy_def id μ, Measure.map_id] at h

end comp

variable {μ} in
/-- Conditional entropy is determined by the joint law. -/
theorem _root_.ProbabilityTheory.IdentDistrib.condEntropy_eq {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {X' : Ω' → S} {Y' : Ω' → T} (hX : Measurable X)
    (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (X' ω, Y' ω)) μ ν) :
    H[X | Y ; μ] = H[X' | Y' ; ν] := by
  have hY : H[Y ; μ] = H[Y' ; ν] := (h.comp measurable_snd).entropy_eq
  linarith [chain_rule μ hX ‹_›, chain_rule ν hX' hY', h.entropy_eq]

/-- Conditional entropy is expected conditional surprisal, each joint atom weighing the
surprisal of its `X`-value under `Y` at its `Y`-value by its mass. -/
theorem condEntropy_eq_sum_negLog (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] = ∑ x, ∑ y, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y})
      * -log ((μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x})) := by
  have hcond (x : S) (y : T) : (μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x})
      = μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) / μ.real (Y ⁻¹' {y}) := by
    rw [cond_real_apply μ (hY (.singleton y)), Set.inter_comm]
  have key (x : S) (y : T) :
      μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * -log ((μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x}))
        = μ.real (Y ⁻¹' {y}) * negMulLog ((μ[|Y ⁻¹' {y}]).real (X ⁻¹' {x})) := by
    rw [hcond]
    obtain hq | hq := eq_or_ne (μ.real (Y ⁻¹' {y})) 0
    · have : μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) = 0 :=
        measureReal_mono_null Set.inter_subset_right hq (measure_ne_top _ _)
      simp [this, hq]
    · simp only [negMulLog]
      field_simp
  rw [condEntropy_eq_sum X hY]
  simp_rw [key]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, entropy_eq_sum hX]

/-- On finite types, conditional entropy vanishes exactly when `X` is almost surely a function
of `Y`. -/
theorem condEntropy_eq_zero_iff [Nonempty S] (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] = 0 ↔ ∃ f : T → S, ∀ᵐ ω ∂μ, X ω = f (Y ω) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · rw [condEntropy_eq_sum X hY μ] at h
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦
      mul_nonneg measureReal_nonneg (entropy_nonneg _ _)).1 h
    have key : ∀ y : T, μ (Y ⁻¹' {y}) ≠ 0 → ∃ x : S, ∀ᵐ ω ∂μ[|Y ⁻¹' {y}], X ω = x := by
      intro y hy
      have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure hy
      refine (entropy_eq_zero_iff hX _).1 ?_
      rcases mul_eq_zero.1 (hzero y (Finset.mem_univ y)) with h0 | h0
      · exact absurd ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0) hy
      · exact h0
    choose g hg using key
    refine ⟨fun y ↦ if hy : μ (Y ⁻¹' {y}) ≠ 0 then g y hy else Classical.arbitrary S, ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun ω hω ↦ ?_)
      (measure_iUnion_null fun y : T ↦ ?_ :
        μ (⋃ y : T, Y ⁻¹' {y} ∩ {ω | X ω ≠
          if hy : μ (Y ⁻¹' {y}) ≠ 0 then g y hy else Classical.arbitrary S}) = 0)
    · exact Set.mem_iUnion.2 ⟨Y ω, rfl, hω⟩
    · rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
      · exact measure_mono_null Set.inter_subset_left hy
      · have hae := hg y hy
        rw [ae_iff, cond_apply (hY (.singleton y))] at hae
        rcases mul_eq_zero.1 hae with h0 | h0
        · exact absurd (ENNReal.inv_eq_zero.1 h0) (measure_ne_top _ _)
        · simpa [dite_eq_left hy] using h0
  · have hfY : Measurable fun ω ↦ f (Y ω) := (measurable_of_finite f).comp hY
    have hpair : (fun ω ↦ (X ω, Y ω)) =ᵐ[μ] fun ω ↦ (f (Y ω), Y ω) :=
      hf.mono fun ω hω ↦ by simp [hω]
    have hid : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (f (Y ω), Y ω)) μ μ :=
      ⟨(hX.prodMk hY).aemeasurable, (hfY.prodMk hY).aemeasurable, Measure.map_congr hpair⟩
    rw [hid.condEntropy_eq hX hY hfY hY]
    exact condEntropy_comp_self μ hY f

/-- On a joint law, the conditional entropy of the first coordinate given the second is the
entropy of the first marginal less the mutual information. -/
theorem condEntropy_fst_snd (ρ : Measure (S × T)) [IsProbabilityMeasure ρ] :
    H[Prod.fst | Prod.snd ; ρ] = Hm[ρ.fst] - Im[ρ] := by
  have h := mutualInfo_eq_entropy_sub_condEntropy ρ measurable_fst measurable_snd
  rw [mutualInfo_eq_measureMutualInfo measurable_fst measurable_snd,
    show (fun p : S × T ↦ (p.1, p.2)) = id from rfl, Measure.map_id] at h
  show _ = H[Prod.fst ; ρ] - Im[ρ]
  linarith

/-- Mutual information is at most the entropy of the second marginal. -/
theorem measureMutualInfo_le_measureEntropy_snd (ρ : Measure (S × T)) [IsProbabilityMeasure ρ] :
    Im[ρ] ≤ Hm[ρ.snd] := by
  have h := mutualInfo_eq_entropy_sub_condEntropy ρ measurable_snd measurable_fst
  rw [mutualInfo_comm ρ measurable_snd measurable_fst,
    mutualInfo_eq_measureMutualInfo measurable_fst measurable_snd,
    show (fun p : S × T ↦ (p.1, p.2)) = id from rfl, Measure.map_id] at h
  rw [h]
  exact sub_le_self _ (condEntropy_nonneg _ _ _)

end entropy

/-! ### Empirical entropies of a finite population

Under the uniform measure on a finite type, entropies are counts. -/

section Empirical

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The entropy of an attribute of a finite population under the uniform measure on a part of
it is the entropy of the attribute's empirical distribution, as counts. -/
theorem entropy_uniformOn [Fintype Ω] {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype S] [DecidableEq S] (A : Finset Ω) (hA : A.Nonempty)
    (X : Ω → S) :
    H[X ; uniformOn (↑A : Set Ω)]
      = ∑ s, negMulLog (((A.filter (X · = s)).card : ℝ) / A.card) := by
  have := isProbabilityMeasure_uniformOn A.finite_toSet (by simpa using hA)
  rw [entropy_eq_sum (measurable_of_finite _)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have h : (↑A ∩ X ⁻¹' {s} : Set Ω) = ↑(A.filter (X · = s)) := by ext ω; simp
  rw [uniformOn_real_apply, h, Set.ncard_coe_finset, Set.ncard_coe_finset]

/-- The conditional entropy of one attribute of a finite population given another, under the
uniform measure, weighs each fibre of `Y` by its share of the population and takes the entropy of
the distribution of `X` on the fibre, all as counts. -/
theorem condEntropy_uniformOn_univ [Fintype Ω] {S T : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype S] [DecidableEq S] [MeasurableSpace T]
    [MeasurableSingletonClass T] [Fintype T] [DecidableEq T] (X : Ω → S) (Y : Ω → T) :
    H[X | Y ; uniformOn (Set.univ : Set Ω)]
      = ∑ y, ((Finset.univ.filter (Y · = y)).card / Fintype.card Ω : ℝ)
          * ∑ x, negMulLog (((Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card
              / (Finset.univ.filter (Y · = y)).card : ℝ)) := by
  have hY : ∀ y, (Y ⁻¹' {y}).ncard = (Finset.univ.filter (Y · = y)).card := fun y ↦ by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have hXY : ∀ y x, (Y ⁻¹' {y} ∩ X ⁻¹' {x}).ncard
      = (Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card := fun y x ↦ by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  rw [condEntropy_eq_sum X (measurable_of_finite Y)]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [uniformOn_univ_cond, entropy_eq_sum (measurable_of_finite X), uniformOn_real_apply,
    Set.univ_inter, Set.ncard_univ, Nat.card_eq_fintype_card]
  simp_rw [uniformOn_real_apply, hY, hXY]

/-- `condEntropy_uniformOn_univ` for attributes valued in finite sets `A` and `B`, the sums running
over those sets. -/
theorem condEntropy_uniformOn_univ_finset [Fintype Ω] {S T : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [DecidableEq S] [MeasurableSpace T] [MeasurableSingletonClass T]
    [DecidableEq T] {X : Ω → S} {Y : Ω → T} {A : Finset S} {B : Finset T} (hX : ∀ ω, X ω ∈ A)
    (hY : ∀ ω, Y ω ∈ B) :
    H[X | Y ; uniformOn (Set.univ : Set Ω)]
      = ∑ y ∈ B, ((Finset.univ.filter (Y · = y)).card / Fintype.card Ω : ℝ)
          * ∑ x ∈ A, negMulLog (((Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card
              / (Finset.univ.filter (Y · = y)).card : ℝ)) := by
  let X' : Ω → A := fun ω ↦ ⟨X ω, hX ω⟩
  let Y' : Ω → B := fun ω ↦ ⟨Y ω, hY ω⟩
  have hval : MeasurableEmbedding (Subtype.val : B → T) :=
    MeasurableEmbedding.subtype_coe B.measurableSet
  have h : H[X | Y ; uniformOn (Set.univ : Set Ω)] = H[X' | Y' ; uniformOn Set.univ] := by
    rw [← condEntropy_comp_of_injective Y' _ (measurable_of_finite _) measurable_subtype_coe
      Subtype.val_injective, ← condEntropy_comp_right_of_measurableEmbedding _ _
      (measurable_of_finite _) hval]
    rfl
  rw [h, condEntropy_uniformOn_univ, ← Finset.sum_coe_sort B]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← Finset.sum_coe_sort A]
  simp only [X', Y', Subtype.ext_iff]

end Empirical

end InformationTheory
