/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.WithDensity
public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior

/-!
# Kernels from a density against a base measure

This file defines `ProbabilityTheory.Kernel.ofDensity`, the kernel whose row at `a` reweights a
base measure by the density `f a` and normalizes. It is Bayes' rule for a likelihood given as a
function: with the prior as base and the likelihood of an observation as density, the row is the
posterior. A row whose density has zero or infinite total mass collapses to the zero measure, so
the kernel is always finite. On a finite target with measurable points the density kernel is the
weight kernel `Kernel.ofWeights` of the density times the base mass of each point, so the
weight-kernel API evaluates its rows.

## Main definitions

* `ProbabilityTheory.Kernel.ofDensity`: row `a` is proportional to `μ.withDensity (f a)`.

## Main results

* `ProbabilityTheory.Kernel.ofDensity_eq_ofWeights`: on a finite target the density kernel is
  the weight kernel of the density times the base mass.
* `ProbabilityTheory.Kernel.ofDensity_indicator_one_apply`: at an indicator density the row is the
  base measure conditioned on the set.
* `ProbabilityTheory.Kernel.ofDensity_div_iSup`: a bounded density may be taken in the unit
  interval, since dividing each row by its supremum leaves the kernel unchanged.
* `ProbabilityTheory.Kernel.ofDensity_uniformOn_univ`: against the uniform prior the density
  kernel is the weight kernel of the density.
* `ProbabilityTheory.Kernel.ofDensity_apply_eq_posterior`: with a kernel's likelihood as density
  the row is the posterior, at every observation of positive marginal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable α]
  [MeasurableSingletonClass α]

/-- The kernel that reweights a base measure by a density and normalizes. Row `a` is the
probability measure proportional to `μ.withDensity (f a)`, and the zero measure when the density
has zero or infinite total mass. -/
noncomputable def ofDensity (μ : Measure β) (f : α → β → ℝ≥0∞) : Kernel α β :=
  ofFunOfCountable fun a ↦ (μ.withDensity (f a))[|Set.univ]

theorem ofDensity_apply (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α) :
    ofDensity μ f a = (μ.withDensity (f a))[|Set.univ] := rfl

instance (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α) :
    IsZeroOrProbabilityMeasure (ofDensity μ f a) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (μ.withDensity (f a))[|Set.univ])

instance (μ : Measure β) (f : α → β → ℝ≥0∞) : IsFiniteKernel (ofDensity μ f) :=
  ⟨⟨1, ENNReal.one_lt_top, fun a ↦ by rw [ofDensity_apply]; exact prob_le_one⟩⟩

theorem isProbabilityMeasure_ofDensity (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α)
    (h0 : ∫⁻ b, f a b ∂μ ≠ 0) (htop : ∫⁻ b, f a b ∂μ ≠ ∞) :
    IsProbabilityMeasure (ofDensity μ f a) := by
  rw [ofDensity_apply]
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;>
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem ofDensity_apply_singleton' [MeasurableSingletonClass β] (μ : Measure β)
    (f : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofDensity μ f a {b} = f a b * μ {b} / ∫⁻ b', f a b' ∂μ := by
  rw [ofDensity_apply, cond_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ (.singleton b), lintegral_singleton, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ENNReal.div_eq_inv_mul]

/-! ### Rescaling the density -/

theorem ofDensity_apply_eq_of_eq_mul (μ : Measure β) {f f' : α → β → ℝ≥0∞} {a : α} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ b, f' a b = c * f a b) :
    ofDensity μ f' a = ofDensity μ f a := by
  rw [ofDensity_apply, ofDensity_apply, show f' a = c • f a from funext h,
    withDensity_smul' c (f a) hc, cond_smul hc0 hc]

/-- Dividing each row's density by its supremum, which puts the density in the unit interval,
leaves the kernel unchanged. -/
theorem ofDensity_div_iSup (μ : Measure β) (f : α → β → ℝ≥0∞) (hf : ∀ a, ⨆ b, f a b ≠ ∞) :
    ofDensity μ (fun a b ↦ f a b / ⨆ b', f a b') = ofDensity μ f := by
  ext a : 1
  rcases eq_or_ne (⨆ b, f a b) 0 with h0 | h0
  · have hfa : f a = 0 := funext fun b ↦ le_antisymm ((le_iSup (f a) b).trans h0.le) zero_le
    simp only [ofDensity_apply, hfa, Pi.zero_apply, ENNReal.zero_div]
    rfl
  · exact ofDensity_apply_eq_of_eq_mul μ (ENNReal.inv_ne_zero.mpr (hf a))
      (ENNReal.inv_ne_top.mpr h0) fun b ↦ by rw [div_eq_mul_inv, mul_comm]

/-! ### Finite targets -/

section Fintype

variable [Fintype β] [MeasurableSingletonClass β]

theorem ofDensity_apply_singleton (μ : Measure β) (f : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofDensity μ f a {b} = f a b * μ {b} / ∑ b', f a b' * μ {b'} := by
  rw [ofDensity_apply_singleton', lintegral_fintype]

/-- On a finite target with measurable points, the density kernel is the weight kernel of the
density times the base mass of each point. -/
theorem ofDensity_eq_ofWeights (μ : Measure β) (f : α → β → ℝ≥0∞) :
    ofDensity μ f = ofWeights fun a b ↦ f a b * μ {b} :=
  Kernel.ext fun a ↦ Measure.ext_of_singleton fun b ↦ by
    rw [ofDensity_apply_singleton, ofWeights_apply_singleton]

/-- Against the counting measure the density kernel is the weight kernel. -/
theorem ofDensity_count (w : α → β → ℝ≥0∞) : ofDensity Measure.count w = ofWeights w := by
  simp only [ofDensity_eq_ofWeights, Measure.count_singleton, mul_one]

theorem ofDensity_real_singleton (μ : Measure β) [IsFiniteMeasure μ] (f : α → β → ℝ≥0∞) (a : α)
    (hf : ∀ b, f a b ≠ ∞) (b : β) :
    (ofDensity μ f a).real {b} =
      (f a b).toReal * μ.real {b} / ∑ b', (f a b').toReal * μ.real {b'} := by
  rw [ofDensity_eq_ofWeights,
    ofWeights_real_singleton _ a fun b ↦ ENNReal.mul_ne_top (hf b) (measure_ne_top _ _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

theorem ofDensity_apply_singleton_ne_zero_iff (μ : Measure β) [IsFiniteMeasure μ]
    {f : α → β → ℝ≥0∞} {a : α} (hf : ∀ b, f a b ≠ ∞) (b : β) :
    ofDensity μ f a {b} ≠ 0 ↔ f a b ≠ 0 ∧ μ {b} ≠ 0 := by
  rw [ofDensity_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, not_or, not_or]
  exact and_iff_left (ENNReal.sum_ne_top.mpr fun b' _ ↦
    ENNReal.mul_ne_top (hf b') (measure_ne_top _ _))

theorem ofDensity_apply_singleton_of_equiv {α' β' : Type*} [MeasurableSpace α']
    [MeasurableSpace β'] [Countable α'] [MeasurableSingletonClass α'] [Fintype β']
    [MeasurableSingletonClass β'] (e : β ≃ β') {μ : Measure β} {μ' : Measure β'}
    {f : α → β → ℝ≥0∞} {f' : α' → β' → ℝ≥0∞} {a : α} {a' : α'} (hμ : ∀ b, μ' {e b} = μ {b})
    (hf : ∀ b, f' a' (e b) = f a b) (b : β) :
    ofDensity μ' f' a' {e b} = ofDensity μ f a {b} := by
  rw [ofDensity_apply_singleton, ofDensity_apply_singleton, hf, hμ, ← e.sum_comp]
  simp only [hf, hμ]

variable [Nonempty β]

/-- Against the uniform prior the density kernel is the weight kernel of the density. -/
theorem ofDensity_uniformOn_univ (f : α → β → ℝ≥0∞) :
    ofDensity (uniformOn Set.univ) f = ofWeights f := by
  rw [ofDensity_eq_ofWeights]
  exact ofWeights_eq_of_mul (c := fun _ ↦ (Fintype.card β : ℝ≥0∞)⁻¹)
    (fun _ ↦ ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    (fun _ ↦ ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero))
    fun _ b ↦ by rw [uniformOn_univ_apply_singleton]

theorem ofDensity_uniformOn_apply_singleton (f : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofDensity (uniformOn Set.univ) f a {b} = f a b / ∑ b', f a b' := by
  rw [ofDensity_uniformOn_univ, ofWeights_apply_singleton]

theorem ofDensity_uniformOn_ofReal_apply_singleton (f : α → β → ℝ) (a : α) (b : β)
    (hf : ∀ b', 0 ≤ f a b') (hpos : 0 < ∑ b', f a b') :
    ofDensity (uniformOn Set.univ) (fun a b ↦ ENNReal.ofReal (f a b)) a {b} =
      ENNReal.ofReal (f a b / ∑ b', f a b') := by
  rw [ofDensity_uniformOn_apply_singleton, ← ENNReal.ofReal_sum_of_nonneg fun b' _ ↦ hf b',
    ← ENNReal.ofReal_div_of_pos hpos]

end Fintype

/-! ### Changing the density and the base -/

/-- At the indicator of a measurable set the row is the base measure conditioned on the set. -/
theorem ofDensity_indicator_one_apply (μ : Measure β) (s : α → Set β) (a : α)
    (hs : MeasurableSet (s a)) : ofDensity μ (fun a ↦ (s a).indicator 1) a = μ[|s a] := by
  rw [ofDensity_apply, withDensity_indicator_one hs]
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]

theorem ofDensity_div [Countable β] [MeasurableSingletonClass β] (μ : Measure β)
    [IsFiniteMeasure μ] (hμ : ∀ b, μ {b} ≠ 0) (ν : α → Measure β) (a : α) :
    ofDensity μ (fun a b ↦ ν a {b} / μ {b}) a = (ν a)[|Set.univ] := by
  rw [ofDensity_apply]
  congr 1
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [withDensity_apply _ (.singleton b), lintegral_singleton,
    ENNReal.div_mul_cancel (hμ b) (measure_ne_top μ _)]

theorem ofDensity_map {γ : Type*} [MeasurableSpace γ] (μ : Measure β) {f : α → γ → ℝ≥0∞}
    {g : β → γ} {a : α} (hf : AEMeasurable (f a) (μ.map g)) (hg : AEMeasurable g μ) :
    (ofDensity μ (fun a ↦ f a ∘ g) a).map g = ofDensity (μ.map g) f a := by
  rw [ofDensity_apply, ofDensity_apply, ← Measure.map_withDensity_comp hf hg,
    cond_map (hg.mono_ac (MeasureTheory.withDensity_absolutelyContinuous _ _)) .univ,
    Set.preimage_univ]

/-- Bayes' rule. With a kernel's likelihood of the observation as density against the prior, the
row at an observation of positive marginal is the posterior. -/
theorem ofDensity_apply_eq_posterior [Countable β] [MeasurableSingletonClass β]
    [StandardBorelSpace β] [Nonempty β] (κ : Kernel β α) [IsFiniteKernel κ] (μ : Measure β)
    [IsFiniteMeasure μ] {a : α} (ha : (κ ∘ₘ μ) {a} ≠ 0) :
    ofDensity μ (fun a b ↦ κ b {a}) a = (κ†μ) a := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [ofDensity_apply_singleton', posterior_apply_singleton κ μ ha,
    Measure.bind_apply (.singleton a) (Kernel.aemeasurable _), mul_comm]

end ProbabilityTheory.Kernel
