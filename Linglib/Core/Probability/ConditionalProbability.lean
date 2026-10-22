/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional probability

Lemmas on mathlib's conditional measure `μ[|s]` that mathlib does not state: monotonicity in
the conditioning event, real-valued forms, pushforwards and products, invariance under scaling
with the composition of two Bayesian updates, and nested events: ratios, the chain rule, and
conditioning up to null sets.
`[UPSTREAM]` candidates for `Mathlib/Probability/ConditionalProbability.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

/-! ### Evaluation lemmas for conditionals -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {s : Set Ω}

/-- Conditioning on a subset that sheds only worlds outside `e` can only raise the conditional
probability of `e`. -/
theorem cond_le_cond_of_subset {u₁ u₂ e : Set Ω} (hu₁ : MeasurableSet u₁)
    (hu₂ : MeasurableSet u₂) (hsub : u₂ ⊆ u₁) (hent : e ∩ u₁ ⊆ u₂) : μ[|u₁] e ≤ μ[|u₂] e := by
  have h : e ∩ u₁ = e ∩ u₂ := Set.inter_congr_left (fun _ hw ↦ hsub hw.2) hent
  rw [cond_apply hu₁, cond_apply hu₂, Set.inter_comm u₁, Set.inter_comm u₂, h]
  exact mul_le_mul_left (ENNReal.inv_le_inv.mpr (measure_mono hsub)) _

/-- The conditional as a ratio of real-valued masses. -/
theorem cond_real_apply (hs : MeasurableSet s) (e : Set Ω) :
    μ[|s].real e = μ.real (s ∩ e) / μ.real s := by
  simp only [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div]

end ProbabilityTheory

/-! ### Pushforwards and products -/

namespace ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}

/-- Conditioning a pushforward on a set is pushing forward the conditional on its preimage. -/
theorem cond_map {f : Ω → Ω'} (hf : AEMeasurable f μ) {s : Set Ω'} (hs : MeasurableSet s) :
    (μ.map f)[|s] = (μ[|f ⁻¹' s]).map f := by
  rw [cond, cond, Measure.map_smul _ hf.restrict, Measure.restrict_map_of_aemeasurable hf hs,
    Measure.map_apply_of_aemeasurable hf hs]

variable (μ) in
/-- Conditioning a product on an event of its first coordinate conditions the first factor. -/
theorem cond_prod_preimage_fst [SFinite μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (s : Set Ω) : (μ.prod ν)[|Prod.fst ⁻¹' s] = μ[|s].prod ν := by
  rw [cond, cond, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ, ← Set.prod_univ,
    Measure.prod_prod, measure_univ, mul_one]

end ProbabilityTheory

/-! ### Sequential conditioning

Conditioning is scale-invariant, so two Bayesian updates compose: reweighting by `f`,
normalizing, reweighting by `g` and normalizing again is one reweighting by `f * g`. -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditioning is invariant under scaling the measure by a positive finite constant. -/
theorem cond_smul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ)[|s] = μ[|s] := by
  simp only [cond, Measure.smul_apply, smul_eq_mul, Measure.restrict_smul, smul_smul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), mul_right_comm, ENNReal.inv_mul_cancel hc0 hc,
    one_mul]

/-- Normalizing after reweighting by `f` and again after reweighting by `g` is normalizing once
after reweighting by `f * g`, so two Bayesian updates compose. -/
theorem cond_univ_withDensity_mul (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hfin : μ.withDensity f Set.univ ≠ ∞) :
    (((μ.withDensity f)[|Set.univ]).withDensity g)[|Set.univ] =
      (μ.withDensity (f * g))[|Set.univ] := by
  rw [withDensity_mul μ hf hg]
  rcases eq_or_ne (μ.withDensity f Set.univ) 0 with h0 | h0
  · have hz : (0 : Measure Ω).withDensity g = 0 :=
      Measure.ext fun s hs ↦ by rw [withDensity_apply _ hs]; simp
    rw [Measure.measure_univ_eq_zero.1 h0,
      cond_eq_zero_of_meas_eq_zero (μ := (0 : Measure Ω)) (s := Set.univ) (by simp), hz]
  · have hc : (μ.withDensity f)[|Set.univ] = (μ.withDensity f Set.univ)⁻¹ • μ.withDensity f := by
      rw [cond, Measure.restrict_univ]
    rw [hc, withDensity_smul_measure,
      cond_smul (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 h0)]

end ProbabilityTheory

/-! ### Nested events

The conditional of an event given a larger one is the ratio of their masses, and conditionals of
nested events chain. Conditioning sees an event only up to a null set, so conditioning on an event
almost contained in another is conditioning the conditional, and the two conditionals are then
comparable. -/

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r s t : Set Ω}

/-- The conditional of an event given a larger one is the ratio of their masses. -/
theorem cond_apply_of_subset (hs : MeasurableSet s) (hts : t ⊆ s) : μ[t | s] = μ t / μ s := by
  rw [cond_apply hs, Set.inter_eq_right.2 hts, ENNReal.div_eq_inv_mul]

/-- The chain rule for nested events. -/
theorem cond_mul_cond_of_subset (hr : MeasurableSet r) (hs : MeasurableSet s) (hsr : s ⊆ r)
    (hts : t ⊆ s) : μ[s | r] * μ[t | s] = μ[t | r] := by
  rw [cond_apply_of_subset hr hsr, cond_apply_of_subset hs hts,
    cond_apply_of_subset hr (hts.trans hsr)]
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [h0, measure_mono_null hts h0]
  rcases eq_or_ne (μ s) ∞ with htop | htop
  · simp [htop, top_le_iff.1 (htop ▸ measure_mono hsr)]
  · rw [mul_comm, ENNReal.div_mul_div_cancel h0 htop]

theorem cond_congr_set (h : s =ᵐ[μ] t) : μ[|s] = μ[|t] := by
  rw [cond, cond, measure_congr h, Measure.restrict_congr_set h]

variable [IsFiniteMeasure μ]

/-- Conditioning on an event almost contained in another is conditioning the conditional. -/
theorem cond_cond_of_ae_le (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ≤ᵐ[μ] t) :
    μ[|t][|s] = μ[|s] := by
  rw [cond_cond_eq_cond_inter ht hs, Set.inter_comm]
  exact cond_congr_set (Filter.inter_eventuallyEqSet_left.2 hst)

/-- One conditional is absolutely continuous with respect to another exactly when the first
event is almost contained in the second. -/
theorem cond_absolutelyContinuous_cond_iff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ[|s] ≪ μ[|t] ↔ s ≤ᵐ[μ] t := by
  refine ⟨fun h ↦ ?_, fun h ↦ cond_cond_of_ae_le hs ht h ▸ cond_absolutelyContinuous⟩
  have h0 : μ[|s] tᶜ = 0 := h (by rw [cond_apply ht, Set.inter_compl_self, measure_empty, mul_zero])
  rw [cond_apply hs, mul_eq_zero, ENNReal.inv_eq_zero] at h0
  exact ae_le_set.2 (h0.resolve_left (measure_ne_top _ _))

end ProbabilityTheory
