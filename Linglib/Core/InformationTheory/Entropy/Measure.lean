/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.KullbackLeibler.Basic
public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Entropy of a measure

The Shannon entropy of a measure, following the PFR project's `ForMathlib` entropy, is
`Hm[μ] = ∑' s, negMulLog (((μ univ)⁻¹ • μ).real {s})`, normalized so that a finite measure has the
entropy of its probability normalization. On a finite type it
[falls short of `log (card S)`](##toReal_klDiv_uniformOn_add_measureEntropy) by the divergence from
the uniform measure, so [only that measure attains the bound](##measureEntropy_eq_log_card_iff). The
mutual information of a measure on a product is `Im[μ] = Hm[μ.fst] + Hm[μ.snd] - Hm[μ]`, on a finite
type [the divergence of the joint from its marginals' product](##measureMutualInfo_eq_toReal_klDiv),
which a [kernel on the second coordinate](##measureMutualInfo_parallelComp_id_comp_le) cannot
increase.

## Implementation notes

`[UPSTREAM]` candidate: mathlib has no Shannon entropy of a measure and no mutual information.

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

theorem measureEntropy_eq_tsum (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _ <;> simp [measureEntropy]

theorem measureEntropy_eq_sum [Fintype S] (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_tsum, tsum_fintype]

/-- The entropy of a probability measure carried by a finite set is a sum over that set. -/
theorem measureEntropy_eq_sum_finset {A : Finset S} (hA : μ (↑A)ᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] : Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_tsum, tsum_eq_sum fun s hs ↦ ?_]
  rw [measureReal_def, measure_mono_null (by simpa using hs) hA, ENNReal.toReal_zero,
    negMulLog_zero]

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
  rw [measureEntropy_eq_sum_finset (A := {x}) (by simp), Finset.sum_singleton]
  simp

/-- The entropy of the uniform measure on a finite set is the logarithm of its cardinality. -/
theorem measureEntropy_uniformOn {A : Finset S} (hA : A.Nonempty) :
    Hm[uniformOn (A : Set S)] = log A.card := by
  classical
  have := isProbabilityMeasure_uniformOn A.finite_toSet (by simpa using hA)
  rw [measureEntropy_eq_sum_finset (A := A)
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

private theorem absolutelyContinuous_uniformOn_univ [Fintype S] [Nonempty S] (μ : Measure S) :
    μ ≪ uniformOn Set.univ :=
  Measure.absolutelyContinuous_of_forall_singleton fun s hs ↦
    absurd hs (uniformOn_univ_singleton_ne_zero s)

/-- The entropy of a probability measure on a finite type falls short of the logarithm of the
cardinality by the divergence from the uniform measure. -/
theorem toReal_klDiv_uniformOn_add_measureEntropy [Fintype S] [Nonempty S] (μ : Measure S)
    [IsProbabilityMeasure μ] :
    (klDiv μ (uniformOn Set.univ)).toReal + Hm[μ] = log (Fintype.card S) := by
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set S)) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  rw [toReal_klDiv_add_measureEntropy (absolutelyContinuous_uniformOn_univ μ)]
  simp_rw [uniformOn_univ_real_singleton, log_inv, mul_neg, Finset.sum_neg_distrib, neg_neg,
    ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

/-- Entropy is at most the logarithm of the cardinality of the type. -/
theorem measureEntropy_le_log_card [Fintype S] (μ : Measure S) :
    Hm[μ] ≤ log (Fintype.card S) := by
  by_cases hμ : IsFiniteMeasure μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simpa using log_natCast_nonneg (Fintype.card S)
    · have : Nonempty S := μ.nonempty_of_neZero
      have h := toReal_klDiv_uniformOn_add_measureEntropy ((μ Set.univ)⁻¹ • μ)
      rw [measureEntropy_univ_smul] at h
      exact h ▸ le_add_of_nonneg_left ENNReal.toReal_nonneg
  · rw [measureEntropy_of_not_isFiniteMeasure hμ]
    exact log_natCast_nonneg _

/-- A probability measure on a finite type has entropy `log (card S)` only if it is uniform. -/
theorem measureEntropy_eq_log_card_iff [Fintype S] [Nonempty S] (μ : Measure S)
    [IsProbabilityMeasure μ] : Hm[μ] = log (Fintype.card S) ↔ μ = uniformOn Set.univ := by
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set S)) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have h := toReal_klDiv_uniformOn_add_measureEntropy μ
  rw [← klDiv_eq_zero_iff]
  refine ⟨fun h' ↦ ((ENNReal.toReal_eq_zero_iff _).1 (by linarith)).resolve_right
    (klDiv_ne_top (absolutelyContinuous_uniformOn_univ μ) .of_finite), fun h' ↦ ?_⟩
  rwa [h', ENNReal.toReal_zero, zero_add] at h

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
  have h (a : S) (b : T) : μ.real {(a, b)} * log ((μ.fst.prod μ.snd).real {(a, b)})
      = μ.real {(a, b)} * log (μ.fst.real {a}) + μ.real {(a, b)} * log (μ.snd.real {b}) := by
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
      rw [log_mul (hpos.trans_le ha).ne' (hpos.trans_le hb).ne', mul_add]
  have h1 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.fst.real {a})
      = ∑ a, μ.fst.real {a} * log (μ.fst.real {a}) := by
    simp_rw [← Finset.sum_mul, ← Measure.fst_real_singleton_eq_sum]
  have h2 : ∑ a, ∑ b, μ.real {(a, b)} * log (μ.snd.real {b})
      = ∑ b, μ.snd.real {b} * log (μ.snd.real {b}) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Measure.snd_real_singleton_eq_sum]
  have key := toReal_klDiv_add_measureEntropy μ.absolutelyContinuous_fst_prod_snd
  simp_rw [Fintype.sum_prod_type, h, Finset.sum_add_distrib, h1, h2] at key
  have hf : Hm[μ.fst] = -∑ a, μ.fst.real {a} * log (μ.fst.real {a}) := by
    rw [measureEntropy_eq_sum]
    simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
  have hs : Hm[μ.snd] = -∑ b, μ.snd.real {b} * log (μ.snd.real {b}) := by
    rw [measureEntropy_eq_sum]
    simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
  rw [measureMutualInfo, hf, hs]
  linarith

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

end InformationTheory
