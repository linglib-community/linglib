/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.MeasureTheory.Measure.GeomMean
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Channel capacity

A channel from inputs `C` to outputs `W` is a Markov kernel `κ : Kernel C W`. An input
distribution `μ` induces the joint law `μ ⊗ₘ κ` and the output marginal `κ ∘ₘ μ`, and the
capacity of the channel is the supremum over input distributions of the mutual information
`Im[μ ⊗ₘ κ]`.

Over finite alphabets the mutual information is the input average of the divergence of each row
`κ c` from the output marginal, and averaging the divergence from any other reference measure
overshoots it by the divergence of the output marginal from that reference (the compensation
identity). An input distribution achieves capacity when no row lies farther from its output
marginal than the information it conveys.

Each row's divergence is also the row's expected log posterior of its input less the input's log
prior, and the Bayesian decoder maximizes that expected log posterior. Hence, taking a fixed input
distribution's expected log posteriors as the exponent, the free energy relative to the uniform
distribution of every input distribution is at most its mutual information less `log |C|`, with
equality at the fixed distribution. The Blahut–Arimoto update gives each input mass proportional
to the geometric mean of its posterior under its row, which on an input distribution of positive
mass everywhere is the uniform distribution tilted by that exponent. By the Gibbs variational
principle the capacity-achieving input distributions of positive mass everywhere are exactly the
fixed points of the update among them, and at such a fixed point every row lies at divergence
exactly the capacity from the output marginal. An input of mass zero that shares an output with
the inputs in use keeps mass zero, so the characterization of the fixed points is confined to
input distributions of positive mass everywhere.

## Main definitions

* `InformationTheory.channelCapacity`: `⨆ μ, Im[μ ⊗ₘ κ]` over probability measures `μ`.
* `InformationTheory.blahutArimoto`: each input weighted by the geometric mean, under its row, of
  its posterior.

## Main results

* `InformationTheory.measureMutualInfo_compProd`, `InformationTheory.sum_mul_toReal_klDiv`:
  `Im[μ ⊗ₘ κ]` is the `μ`-average of the divergences `klDiv (κ c) (κ ∘ₘ μ)`, and the
  compensation identity.
* `InformationTheory.sum_mul_integral_log_le`: the Bayesian decoder maximizes the expected log
  posterior of the input.
* `InformationTheory.eq_channelCapacity_iff_eq_tilted`: the capacity-achieving input
  distributions of positive mass everywhere are the uniform distribution tilted by their own
  expected log posteriors.
* `InformationTheory.blahutArimoto_eq_tilted`: on input distributions of positive mass
  everywhere the update is that tilt.
* `InformationTheory.eq_blahutArimoto_iff`: an input distribution of positive mass everywhere
  achieves capacity exactly when it is a Blahut–Arimoto fixed point.

## References

* [C. E. Shannon, *A Mathematical Theory of Communication* (1948)][shannon-1948]
* [R. E. Blahut, *Computation of channel capacity and rate-distortion functions*
  (1972)][blahut-1972]
* [S. Arimoto, *An algorithm for computing the capacity of arbitrary discrete memoryless
  channels* (1972)][arimoto-1972]
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2006)][cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {C W : Type*} [MeasurableSpace C] [MeasurableSpace W] [Fintype C] [Fintype W]
  [MeasurableSingletonClass C] [MeasurableSingletonClass W]

/-- The capacity of a channel is the supremum over input distributions of the mutual information
between its input and output. -/
noncomputable def channelCapacity (κ : Kernel C W) : ℝ :=
  ⨆ μ : ProbabilityMeasure C, Im[(μ : Measure C) ⊗ₘ κ]

/-- The Blahut–Arimoto update of an input distribution gives each input mass proportional to the
geometric mean, under its row of the channel, of its posterior given the output,
`∏ w, q(c | w) ^ κ(w | c)` ([blahut-1972], [arimoto-1972]). -/
noncomputable def blahutArimoto [Nonempty C] (κ : Kernel C W) [IsFiniteKernel κ] (μ : Measure C)
    [IsFiniteMeasure μ] : Measure C :=
  Kernel.ofWeights (fun (_ : Unit) c ↦ (κ c).geomMean fun w ↦ (κ†μ) w {c}) ()

private theorem comp_absolutelyContinuous (κ : Kernel C W) (μ : Measure C) {q : Measure W}
    (hq : ∀ c, μ {c} ≠ 0 → κ c ≪ q) : κ ∘ₘ μ ≪ q :=
  Measure.absolutelyContinuous_of_forall_singleton fun w hw ↦ by
    rw [Measure.comp_apply_singleton]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    obtain hc | hc := eq_or_ne (μ {c}) 0
    · rw [hc, zero_mul]
    · rw [hq c hc hw, mul_zero]

private theorem freeEnergy_uniformOn [Nonempty C] (ν : Measure C) [IsProbabilityMeasure ν]
    (f : C → ℝ) : (uniformOn Set.univ).freeEnergy f ν
      = ∑ c, ν.real {c} * (f c - log (ν.real {c})) - log (Fintype.card C) := by
  have hac : ν ≪ uniformOn Set.univ := Measure.absolutelyContinuous_of_forall_singleton
    fun c h ↦ absurd h (uniformOn_univ_singleton_ne_zero c)
  have := isProbabilityMeasure_uniformOn (Set.finite_univ (α := C)) Set.univ_nonempty
  rw [Measure.freeEnergy, integral_fintype .of_finite, toReal_klDiv_eq_sum_log_div hac,
    show log (Fintype.card C : ℝ) = ∑ c, ν.real {c} * log (Fintype.card C) by
      rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul],
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  obtain hc | hc := eq_or_ne (ν.real {c}) 0
  · simp [hc]
  rw [uniformOn_univ_real_singleton, div_inv_eq_mul,
    log_mul hc (Nat.cast_ne_zero.2 Fintype.card_ne_zero), smul_eq_mul]
  ring

variable (κ : Kernel C W) [IsMarkovKernel κ] (μ : Measure C) [IsProbabilityMeasure μ]

theorem condEntropy_snd_fst_compProd :
    H[Prod.snd | Prod.fst ; μ ⊗ₘ κ] = ∑ c, μ.real {c} * Hm[κ c] := by
  rw [condEntropy_eq_sum _ measurable_fst]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hfst : (μ ⊗ₘ κ).real (Prod.fst ⁻¹' {c}) = μ.real {c} := by
    rw [measureReal_def, ← Measure.fst_apply (.singleton c), Measure.fst_compProd, measureReal_def]
  rw [hfst]
  rcases eq_or_ne (μ {c}) 0 with h | h
  · simp [measureReal_def, h]
  · rw [entropy_def, Measure.map_snd_cond_fst_compProd μ κ h]

private theorem measureMutualInfo_compProd_eq_sum :
    Im[μ ⊗ₘ κ] = ∑ c, μ.real {c} * ∑ w, (κ c).real {w}
      * log ((κ c).real {w} / (κ ∘ₘ μ).real {w}) := by
  rw [measureMutualInfo_eq_toReal_klDiv,
    toReal_klDiv_eq_sum_log_div (Measure.absolutelyContinuous_fst_prod_snd _),
    Measure.fst_compProd, Measure.snd_compProd, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Measure.compProd_real_singleton, Measure.prod_real_singleton]
  obtain hc | hc := eq_or_ne (μ.real {c}) 0
  · simp [hc]
  · rw [mul_div_mul_left _ _ hc, mul_assoc]

/-- The compensation identity. Averaging the divergence of the rows of a channel from a
reference measure overshoots the mutual information by the divergence of the output marginal
from that reference. -/
theorem sum_mul_toReal_klDiv (q : Measure W) [IsProbabilityMeasure q]
    (hq : ∀ c, μ {c} ≠ 0 → κ c ≪ q) :
    ∑ c, μ.real {c} * (klDiv (κ c) q).toReal = Im[μ ⊗ₘ κ] + (klDiv (κ ∘ₘ μ) q).toReal := by
  have key (c : C) (w : W) :
      μ.real {c} * ((κ c).real {w} * log ((κ c).real {w} / q.real {w}))
        = μ.real {c} * ((κ c).real {w} * log ((κ c).real {w} / (κ ∘ₘ μ).real {w}))
          + μ.real {c} * (κ c).real {w} * log ((κ ∘ₘ μ).real {w} / q.real {w}) := by
    obtain h0 | h0 := eq_or_ne (μ.real {c} * (κ c).real {w}) 0
    · rcases mul_eq_zero.mp h0 with h | h <;> simp [h]
    obtain ⟨hc, hk⟩ := mul_ne_zero_iff.mp h0
    have hq : q.real {w} ≠ 0 := by
      rw [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)] at hc hk ⊢
      exact fun h ↦ hk (hq c hc h)
    have hr : (κ ∘ₘ μ).real {w} ≠ 0 := by
      refine (lt_of_lt_of_le (lt_of_le_of_ne (by positivity) (Ne.symm h0)) ?_).ne'
      rw [Measure.comp_real_singleton]
      exact Finset.single_le_sum (f := fun c ↦ μ.real {c} * (κ c).real {w})
        (fun _ _ ↦ by positivity) (Finset.mem_univ c)
    rw [← div_mul_div_cancel₀ hr, log_mul (div_ne_zero hk hr) (div_ne_zero hr hq)]
    ring
  rw [measureMutualInfo_compProd_eq_sum,
    toReal_klDiv_eq_sum_log_div (comp_absolutelyContinuous κ μ hq)]
  calc ∑ c, μ.real {c} * (klDiv (κ c) q).toReal
      = ∑ c, ∑ w, μ.real {c} * ((κ c).real {w} * log ((κ c).real {w} / q.real {w})) := by
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        obtain hc | hc := eq_or_ne (μ {c}) 0
        · simp [measureReal_def, hc]
        · rw [toReal_klDiv_eq_sum_log_div (hq c hc), Finset.mul_sum]
    _ = _ := by
        simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm (f := fun c w ↦ μ.real {c} * (κ c).real {w}
          * log ((κ ∘ₘ μ).real {w} / q.real {w}))]
        simp_rw [← Finset.sum_mul, ← Measure.comp_real_singleton]

/-- Mutual information across a channel is the input average of the divergence of each row from
the output marginal. -/
theorem measureMutualInfo_compProd :
    Im[μ ⊗ₘ κ] = ∑ c, μ.real {c} * (klDiv (κ c) (κ ∘ₘ μ)).toReal := by
  rw [sum_mul_toReal_klDiv κ μ _ fun c hc ↦ κ.absolutelyContinuous_comp μ hc, klDiv_self,
    ENNReal.toReal_zero, add_zero]

theorem measureMutualInfo_compProd_le_log_card : Im[μ ⊗ₘ κ] ≤ log (Fintype.card W) :=
  (measureMutualInfo_le_measureEntropy_snd _).trans (measureEntropy_le_log_card _)

theorem channelCapacity_le_log_card : channelCapacity κ ≤ log (Fintype.card W) :=
  Real.iSup_le (fun μ ↦ measureMutualInfo_compProd_le_log_card κ μ) (log_natCast_nonneg _)

theorem channelCapacity_nonneg : 0 ≤ channelCapacity κ :=
  Real.iSup_nonneg fun _ ↦ measureMutualInfo_nonneg _

theorem measureMutualInfo_compProd_le_channelCapacity : Im[μ ⊗ₘ κ] ≤ channelCapacity κ :=
  le_ciSup (f := fun μ : ProbabilityMeasure C ↦ Im[(μ : Measure C) ⊗ₘ κ])
    ⟨log (Fintype.card W), by
      rintro _ ⟨μ, rfl⟩
      exact measureMutualInfo_compProd_le_log_card κ μ⟩ ⟨μ, inferInstance⟩

theorem measureMutualInfo_compProd_eq_channelCapacity
    (h : ∀ c, klDiv (κ c) (κ ∘ₘ μ) ≤ ENNReal.ofReal (Im[μ ⊗ₘ κ])) :
    Im[μ ⊗ₘ κ] = channelCapacity κ := by
  refine le_antisymm (measureMutualInfo_compProd_le_channelCapacity κ μ)
    (Real.iSup_le (fun ν ↦ ?_) (measureMutualInfo_nonneg _))
  have hac (c : C) : κ c ≪ κ ∘ₘ μ := by
    by_contra hc
    exact ENNReal.ofReal_ne_top (top_le_iff.mp (klDiv_of_not_ac hc ▸ h c))
  calc Im[(ν : Measure C) ⊗ₘ κ]
      ≤ ∑ c, (ν : Measure C).real {c} * (klDiv (κ c) (κ ∘ₘ μ)).toReal := by
        rw [sum_mul_toReal_klDiv κ ν (κ ∘ₘ μ) fun c _ ↦ hac c]
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    _ ≤ ∑ c, (ν : Measure C).real {c} * Im[μ ⊗ₘ κ] :=
        Finset.sum_le_sum fun c _ ↦ mul_le_mul_of_nonneg_left
          (ENNReal.toReal_le_of_le_ofReal (measureMutualInfo_nonneg _) (h c)) measureReal_nonneg
    _ = Im[μ ⊗ₘ κ] := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

theorem toReal_klDiv_eq_integral_log_sub [Nonempty C] {c : C} (hc : μ {c} ≠ 0) :
    (klDiv (κ c) (κ ∘ₘ μ)).toReal = ∫ w, log (((κ†μ) w).real {c}) ∂(κ c) - log (μ.real {c}) := by
  have hpc : μ.real {c} ≠ 0 := by rwa [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)]
  rw [toReal_klDiv_eq_sum_log_div (κ.absolutelyContinuous_comp μ hc), integral_fintype .of_finite,
    show log (μ.real {c}) = ∑ w, (κ c).real {w} * log (μ.real {c}) by
      rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul],
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  obtain hk | hk := eq_or_ne ((κ c).real {w}) 0
  · simp [hk]
  have hw' : (κ ∘ₘ μ).real {w} ≠ 0 := by
    rw [Measure.comp_real_singleton]
    refine (lt_of_lt_of_le (mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hpc))
      (lt_of_le_of_ne measureReal_nonneg (Ne.symm hk))) ?_).ne'
    exact Finset.single_le_sum (f := fun c ↦ μ.real {c} * (κ c).real {w})
      (fun _ _ ↦ by positivity) (Finset.mem_univ c)
  have hw : (κ ∘ₘ μ) {w} ≠ 0 := by rwa [Ne, ← measureReal_eq_zero_iff (measure_ne_top _ _)]
  rw [smul_eq_mul, posterior_real_singleton κ μ hw, log_div (mul_ne_zero hpc hk) hw',
    log_mul hpc hk, log_div hk hw']
  ring

/-- The Bayesian decoder maximizes the expected log score of the input. No decoder that charges
every input the posterior charges does better, even one that gives no guess at some outputs. -/
theorem sum_mul_integral_log_le [Nonempty C] (φ : W → Measure C)
    [∀ w, IsZeroOrProbabilityMeasure (φ w)] (hφ : ∀ w, (κ ∘ₘ μ) {w} ≠ 0 → (κ†μ) w ≪ φ w) :
    ∑ c, μ.real {c} * ∫ w, log ((φ w).real {c}) ∂(κ c)
      ≤ ∑ c, μ.real {c} * ∫ w, log (((κ†μ) w).real {c}) ∂(κ c) := by
  rw [← sub_nonneg]
  have key : ∑ c, μ.real {c} * ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)
        - ∑ c, μ.real {c} * ∫ w, log ((φ w).real {c}) ∂(κ c)
      = ∑ w, (κ ∘ₘ μ).real {w} * (klDiv ((κ†μ) w) (φ w)).toReal := by
    simp only [integral_fintype .of_finite, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hb (c : C) : μ.real {c} * ((κ c).real {w} * log (((κ†μ) w).real {c}))
          - μ.real {c} * ((κ c).real {w} * log ((φ w).real {c}))
        = (κ ∘ₘ μ).real {w} * (((κ†μ) w).real {c}
          * (log (((κ†μ) w).real {c}) - log ((φ w).real {c}))) := by
      linear_combination (log ((φ w).real {c}) - log (((κ†μ) w).real {c}))
        * comp_real_mul_posterior_real κ μ c w
    simp_rw [hb, ← Finset.mul_sum]
    obtain hw | hw := eq_or_ne ((κ ∘ₘ μ) {w}) 0
    · rw [measureReal_def, hw, ENNReal.toReal_zero, zero_mul, zero_mul]
    have : IsProbabilityMeasure (φ w) := (eq_zero_or_isProbabilityMeasure (φ w)).resolve_left
      fun h0 ↦ NeZero.ne ((κ†μ) w) (Measure.measure_univ_eq_zero.1 (hφ w hw (by rw [h0]; rfl)))
    rw [toReal_klDiv_eq_sum_log_div (hφ w hw)]
    congr 1
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    obtain hp | hp := eq_or_ne (((κ†μ) w).real {c}) 0
    · simp [hp]
    have hφc : (φ w).real {c} ≠ 0 := fun h ↦ hp <|
      (measureReal_eq_zero_iff (measure_ne_top _ _)).2
        (hφ w hw ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h))
    rw [log_div hp hφc]
  rw [key]
  exact Finset.sum_nonneg fun w _ ↦ mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg

/-! ### The Blahut–Arimoto fixed point -/

section BlahutArimoto

variable [Nonempty C]

instance : IsProbabilityMeasure (blahutArimoto κ μ) := by
  obtain ⟨c, hc⟩ : ∃ c, μ {c} ≠ 0 := by
    by_contra! h
    exact NeZero.ne μ (Measure.ext_iff_singleton.2 fun c ↦ by simp [h c])
  unfold blahutArimoto
  exact Kernel.isProbabilityMeasure_ofWeights ⟨c, Measure.geomMean_ne_zero fun w hw ↦
    (posterior_apply_singleton_ne_zero_iff κ μ (Measure.comp_apply_singleton_ne_zero κ μ hc hw)
      c).2 ⟨hc, hw⟩⟩ fun _ ↦ Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _

/-- An input of mass zero that shares an output with the inputs in use keeps mass zero. -/
theorem blahutArimoto_apply_singleton_eq_zero {c : C} (hc : μ {c} = 0) {w : W}
    (hw : κ c {w} ≠ 0) (hμw : (κ ∘ₘ μ) {w} ≠ 0) : blahutArimoto κ μ {c} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (Measure.geomMean_eq_zero_iff.2
    ⟨w, hw, by rw [posterior_apply_singleton κ μ hμw, hc, zero_mul, ENNReal.zero_div]⟩)

/-- On an input distribution of positive mass everywhere, the Blahut–Arimoto update is the
uniform distribution tilted by each input's expected log posterior. -/
theorem blahutArimoto_eq_tilted (hμ : ∀ c, μ {c} ≠ 0) :
    blahutArimoto κ μ =
      (uniformOn Set.univ).tilted fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c) := by
  rw [uniformOn_univ_tilted]
  unfold blahutArimoto
  refine Kernel.ofWeights_apply_eq_tilted Measure.count fun c ↦ ?_
  rw [Measure.count_singleton, one_mul, Measure.geomMean_eq_ofReal_exp_sum_log
      (fun w hw ↦ (posterior_apply_singleton_ne_zero_iff κ μ
        (Measure.comp_apply_singleton_ne_zero κ μ (hμ c) hw) c).2 ⟨hμ c, hw⟩)
      (fun _ _ ↦ measure_ne_top _ _), integral_fintype .of_finite]
  simp only [smul_eq_mul, measureReal_def]

private theorem measureMutualInfo_compProd_eq_sum_log :
    Im[μ ⊗ₘ κ] = ∑ c, μ.real {c}
      * (∫ w, log (((κ†μ) w).real {c}) ∂(κ c) - log (μ.real {c})) := by
  rw [measureMutualInfo_compProd]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  obtain hc | hc := eq_or_ne (μ {c}) 0
  · simp [measureReal_def, hc]
  rw [toReal_klDiv_eq_integral_log_sub κ μ hc]

private theorem toReal_klDiv_of_eq_tilted
    (h : μ = (uniformOn Set.univ).tilted fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)) (c : C) :
    (klDiv (κ c) (κ ∘ₘ μ)).toReal
      = log (∑ c', exp (∫ w, log (((κ†μ) w).real {c'}) ∂(κ c'))) := by
  have hreal (c : C) :
      μ.real {c} = softmax (fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)) c := by
    rw [congrArg (·.real {c}) h, uniformOn_univ_tilted, count_tilted_real_singleton]
  have hc : μ {c} ≠ 0 := by
    rw [← measureReal_ne_zero_iff (measure_ne_top _ _), hreal]
    exact (softmax_pos _ c).ne'
  rw [toReal_klDiv_eq_integral_log_sub κ μ hc, hreal, log_softmax]
  ring

/-- An input distribution achieves capacity with positive mass everywhere exactly when it is the
uniform distribution tilted by each input's expected log posterior. -/
theorem eq_channelCapacity_iff_eq_tilted :
    (Im[μ ⊗ₘ κ] = channelCapacity κ ∧ ∀ c, μ {c} ≠ 0) ↔
      μ = (uniformOn Set.univ).tilted fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c) := by
  have := isProbabilityMeasure_uniformOn (Set.finite_univ (α := C)) Set.univ_nonempty
  constructor
  · rintro ⟨h, hμ⟩
    -- the free energy of every input distribution, tilted by `μ`'s expected log posterior,
    -- is at most its mutual information, with equality at `μ`
    have hfe (ν : Measure C) [IsProbabilityMeasure ν] : (uniformOn Set.univ).freeEnergy
        (fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)) ν + log (Fintype.card C)
          ≤ Im[ν ⊗ₘ κ] := by
      rw [freeEnergy_uniformOn, measureMutualInfo_compProd_eq_sum_log, sub_add_cancel]
      simp only [mul_sub, Finset.sum_sub_distrib, sub_le_sub_iff_right]
      refine sum_mul_integral_log_le κ ν (κ†μ) fun w hw ↦ ?_
      refine Measure.absolutelyContinuous_of_forall_singleton fun c hc ↦ ?_
      obtain ⟨c', hc', hk'⟩ : ∃ c', ν {c'} ≠ 0 ∧ κ c' {w} ≠ 0 := by
        by_contra! h0
        apply hw
        rw [Measure.comp_apply_singleton]
        refine Finset.sum_eq_zero fun c' _ ↦ ?_
        by_cases hν : ν {c'} = 0
        · rw [hν, zero_mul]
        · rw [h0 c' hν, mul_zero]
      have hμw : (κ ∘ₘ μ) {w} ≠ 0 := Measure.comp_apply_singleton_ne_zero κ μ (hμ c') hk'
      by_contra hne
      exact (posterior_apply_singleton_ne_zero_iff κ μ hμw c).2
        ⟨hμ c, ((posterior_apply_singleton_ne_zero_iff κ ν hw c).1 hne).2⟩ hc
    have hμeq : (uniformOn Set.univ).freeEnergy
        (fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)) μ + log (Fintype.card C)
          = Im[μ ⊗ₘ κ] := by
      rw [freeEnergy_uniformOn, measureMutualInfo_compProd_eq_sum_log, sub_add_cancel]
    have : IsProbabilityMeasure ((uniformOn Set.univ).tilted
        fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)) := isProbabilityMeasure_tilted .of_finite
    refine eq_tilted_of_freeEnergy_eq_cgf _ _ (Measure.absolutelyContinuous_of_forall_singleton
      fun c h ↦ absurd h (uniformOn_univ_singleton_ne_zero c)) .of_finite .of_finite .of_finite
      (le_antisymm (freeEnergy_le_cgf _ _ (Measure.absolutelyContinuous_of_forall_singleton
        fun c h ↦ absurd h (uniformOn_univ_singleton_ne_zero c)) .of_finite .of_finite
        .of_finite) ?_)
    rw [← freeEnergy_tilted (uniformOn Set.univ) .of_finite .of_finite .of_finite]
    linarith [hfe ((uniformOn Set.univ).tilted fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c)),
      measureMutualInfo_compProd_le_channelCapacity κ
        ((uniformOn Set.univ).tilted fun c ↦ ∫ w, log (((κ†μ) w).real {c}) ∂(κ c))]
  · intro h
    have hD := toReal_klDiv_of_eq_tilted κ μ h
    have hI : Im[μ ⊗ₘ κ] = log (∑ c', exp (∫ w, log (((κ†μ) w).real {c'}) ∂(κ c'))) := by
      rw [measureMutualInfo_compProd, Finset.sum_congr rfl fun c _ ↦ by rw [hD c],
        ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]
    have hμ (c : C) : μ {c} ≠ 0 := by
      rw [h]
      exact fun h0 ↦ uniformOn_univ_singleton_ne_zero c (absolutelyContinuous_tilted .of_finite h0)
    refine ⟨measureMutualInfo_compProd_eq_channelCapacity κ μ fun c ↦ ?_, hμ⟩
    rw [hI, ← hD c, ENNReal.ofReal_toReal]
    exact klDiv_ne_top (κ.absolutelyContinuous_comp μ (hμ c)) .of_finite

/-- An input distribution of positive mass everywhere achieves capacity exactly when it is a fixed
point of the Blahut–Arimoto update ([blahut-1972], [arimoto-1972]). -/
theorem eq_blahutArimoto_iff (hμ : ∀ c, μ {c} ≠ 0) :
    Im[μ ⊗ₘ κ] = channelCapacity κ ↔ μ = blahutArimoto κ μ := by
  rw [blahutArimoto_eq_tilted κ μ hμ, ← eq_channelCapacity_iff_eq_tilted κ μ, and_iff_left hμ]

theorem toReal_klDiv_eq_channelCapacity (hμ : ∀ c, μ {c} ≠ 0)
    (h : Im[μ ⊗ₘ κ] = channelCapacity κ) (c : C) :
    (klDiv (κ c) (κ ∘ₘ μ)).toReal = channelCapacity κ := by
  have hD := toReal_klDiv_of_eq_tilted κ μ ((eq_channelCapacity_iff_eq_tilted κ μ).1 ⟨h, hμ⟩)
  rw [← h, measureMutualInfo_compProd, Finset.sum_congr rfl fun c _ ↦ by rw [hD c],
    ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul, hD c]

end BlahutArimoto

end InformationTheory
