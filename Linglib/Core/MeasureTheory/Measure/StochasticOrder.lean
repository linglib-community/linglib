/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.ProductMeasure

/-!
# The stochastic order on measures

On a preordered measurable space, `μ ≤ₛₜ ν` says that `ν` gives every measurable upper set at
least the mass `μ` does: `ν` sits higher in the order. The relation is preserved by
[pushing forward along a monotone map](##MeasureTheory.Measure.StochasticLE.map), and it is what
makes [the integral of a monotone function](##MeasureTheory.Measure.StochasticLE.integral_le)
monotone in the measure.

The order is usually established through a coupling: two random variables on one probability
space with the given laws, the first almost surely below the second
([`stochasticLE_map_of_ae_le`](##MeasureTheory.Measure.stochasticLE_map_of_ae_le)). Couplings of
the coordinates assemble into a coupling of the product, so the order passes to
[product measures](##MeasureTheory.Measure.stochasticLE_infinitePi).

## TODO

Strassen's theorem, that on a Polish space the stochastic order yields a monotone coupling, is
not stated.
-/

public section

open Set Function
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] {mΩ : MeasurableSpace Ω}
  [Preorder α] [Preorder β] {μ ν ξ : Measure α}

/-- The stochastic order: `ν` gives every measurable upper set at least the mass `μ` does. -/
def StochasticLE (μ ν : Measure α) : Prop :=
  ∀ ⦃U : Set α⦄, IsUpperSet U → MeasurableSet U → μ U ≤ ν U

@[inherit_doc] scoped infix:50 " ≤ₛₜ " => StochasticLE

/-- The layer-cake formula for the positive part of a measurable function. -/
private theorem lintegral_ofReal_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hfm : Measurable f) :
    ∫⁻ a, .ofReal (f a) ∂μ = ∫⁻ t in Ioi 0, μ {a | t < max (f a) 0} :=
  (lintegral_congr fun a ↦ by simp [ENNReal.ofReal_max]).trans <|
    lintegral_eq_lintegral_meas_lt μ (f := fun a ↦ max (f a) 0)
      (.of_forall fun _ ↦ le_max_right _ _) (hfm.max measurable_const).aemeasurable

namespace StochasticLE

protected theorem refl (μ : Measure α) : μ ≤ₛₜ μ := fun _ _ _ ↦ le_rfl

protected theorem trans (h₁ : μ ≤ₛₜ ν) (h₂ : ν ≤ₛₜ ξ) : μ ≤ₛₜ ξ :=
  fun _ hU hUm ↦ (h₁ hU hUm).trans (h₂ hU hUm)

instance : Std.Refl (α := Measure α) (· ≤ₛₜ ·) := ⟨StochasticLE.refl⟩

instance : IsTrans (Measure α) (· ≤ₛₜ ·) := ⟨fun _ _ _ ↦ StochasticLE.trans⟩

/-- Pushing forward along a monotone map preserves the stochastic order. -/
protected theorem map (h : μ ≤ₛₜ ν) {f : α → β} (hf : Monotone f) (hfm : Measurable f) :
    μ.map f ≤ₛₜ ν.map f := fun U hU hUm ↦ by
  rw [map_apply hfm hUm, map_apply hfm hUm]
  exact h (hU.preimage hf) (hfm hUm)

/-- A map that agrees almost everywhere with a monotone one preserves the stochastic order. -/
theorem map_of_ae_eq (h : μ ≤ₛₜ ν) {f g : α → β} (hg : Monotone g) (hgm : Measurable g)
    (hμ : f =ᵐ[μ] g) (hν : f =ᵐ[ν] g) : μ.map f ≤ₛₜ ν.map f := by
  rw [map_congr hμ, map_congr hν]
  exact h.map hg hgm

/-- Measures of equal finite mass in the stochastic order compare on lower sets the other way. -/
theorem measure_le_of_isLowerSet [IsFiniteMeasure μ] (h : μ ≤ₛₜ ν) (huniv : μ univ = ν univ)
    {L : Set α} (hL : IsLowerSet L) (hLm : MeasurableSet L) : ν L ≤ μ L := by
  have hν : ν Lᶜ ≠ ∞ := ((measure_mono (subset_univ _)).trans_lt
    (huniv ▸ measure_lt_top μ univ)).ne
  refine ENNReal.le_of_add_le_add_right hν ?_
  rw [measure_add_measure_compl hLm, ← huniv, ← measure_add_measure_compl hLm]
  exact add_le_add le_rfl (h hL.compl hLm.compl)

/-- The lower integral of the positive part of a monotone function is monotone in the measure. -/
theorem lintegral_ofReal_le (h : μ ≤ₛₜ ν) {f : α → ℝ} (hf : Monotone f) (hfm : Measurable f) :
    ∫⁻ a, .ofReal (f a) ∂μ ≤ ∫⁻ a, .ofReal (f a) ∂ν := by
  rw [lintegral_ofReal_eq μ hfm, lintegral_ofReal_eq ν hfm]
  exact lintegral_mono fun t ↦ h (fun a b hab ha ↦ lt_of_lt_of_le ha
    (max_le_max_right 0 (hf hab)))
    (measurableSet_lt measurable_const (hfm.max measurable_const))

/-- The lower integral of the positive part of an antitone function is antitone in the measure,
between measures of equal finite mass. -/
theorem lintegral_ofReal_le_of_antitone [IsFiniteMeasure μ] (h : μ ≤ₛₜ ν)
    (huniv : μ univ = ν univ) {f : α → ℝ} (hf : Antitone f) (hfm : Measurable f) :
    ∫⁻ a, .ofReal (f a) ∂ν ≤ ∫⁻ a, .ofReal (f a) ∂μ := by
  rw [lintegral_ofReal_eq μ hfm, lintegral_ofReal_eq ν hfm]
  exact lintegral_mono fun t ↦ h.measure_le_of_isLowerSet huniv (fun a b hab ha ↦
    lt_of_lt_of_le ha (max_le_max_right 0 (hf hab)))
    (measurableSet_lt measurable_const (hfm.max measurable_const))

/-- The integral of a monotone function is monotone in the measure, between measures of equal
finite mass. -/
theorem integral_le [IsFiniteMeasure μ] (h : μ ≤ₛₜ ν) (huniv : μ univ = ν univ) {f : α → ℝ}
    (hf : Monotone f) (hfm : Measurable f) (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ a, f a ∂μ ≤ ∫ a, f a ∂ν := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hν]
  exact sub_le_sub
    (ENNReal.toReal_mono ((lintegral_mono fun _ ↦ Real.ofReal_le_enorm _).trans_lt hν.2).ne
      (h.lintegral_ofReal_le hf hfm))
    (ENNReal.toReal_mono ((lintegral_mono fun _ ↦ Real.ofReal_le_enorm _).trans_lt hμ.neg.2).ne
      (h.lintegral_ofReal_le_of_antitone huniv hf.neg hfm.neg))

/-- The integral of an antitone function is antitone in the measure, between measures of equal
finite mass. -/
theorem integral_le_of_antitone [IsFiniteMeasure μ] (h : μ ≤ₛₜ ν) (huniv : μ univ = ν univ)
    {f : α → ℝ} (hf : Antitone f) (hfm : Measurable f) (hμ : Integrable f μ)
    (hν : Integrable f ν) : ∫ a, f a ∂ν ≤ ∫ a, f a ∂μ := by
  simpa [integral_neg] using h.integral_le huniv hf.neg hfm.neg hμ.neg hν.neg

end StochasticLE

/-- Two random variables on one space, the first almost surely below the second, have
stochastically ordered laws. -/
theorem stochasticLE_map_of_ae_le {P : Measure Ω} {X Y : Ω → α} (hX : Measurable X)
    (hY : Measurable Y) (h : X ≤ᵐ[P] Y) : P.map X ≤ₛₜ P.map Y := fun U hU hUm ↦ by
  rw [map_apply hX hUm, map_apply hY hUm]
  exact measure_mono_ae (h.mono fun _ hω hXω ↦ hU hω hXω)

/-- A monotone coupling of `μ` and `ν`: a measure on pairs with marginals `μ` and `ν` under which
the first coordinate is almost surely below the second. -/
structure IsMonotoneCoupling (γ : Measure (α × α)) (μ ν : Measure α) : Prop where
  map_fst : γ.map Prod.fst = μ
  map_snd : γ.map Prod.snd = ν
  ae_le : ∀ᵐ z ∂γ, z.1 ≤ z.2

namespace IsMonotoneCoupling

variable {γ : Measure (α × α)}

/-- Measures with a monotone coupling are stochastically ordered. -/
theorem stochasticLE (h : IsMonotoneCoupling γ μ ν) : μ ≤ₛₜ ν :=
  h.map_fst ▸ h.map_snd ▸ stochasticLE_map_of_ae_le measurable_fst measurable_snd h.ae_le

theorem isProbabilityMeasure [IsProbabilityMeasure μ] (h : IsMonotoneCoupling γ μ ν) :
    IsProbabilityMeasure γ :=
  ⟨by rw [← preimage_univ (f := Prod.fst), ← map_apply measurable_fst .univ, h.map_fst,
    measure_univ]⟩

end IsMonotoneCoupling

section InfinitePi

variable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  [∀ i, Preorder (X i)] {μ ν : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- Monotone couplings of the coordinates give the stochastic order between countable products. -/
theorem stochasticLE_infinitePi {γ : ∀ i, Measure (X i × X i)}
    (h : ∀ i, IsMonotoneCoupling (γ i) (μ i) (ν i)) : infinitePi μ ≤ₛₜ infinitePi ν := by
  have := fun i ↦ (h i).isProbabilityMeasure
  have hμ : infinitePi μ = (infinitePi γ).map fun ω i ↦ (ω i).1 := by
    rw [infinitePi_map_pi γ (f := fun _ ↦ Prod.fst) fun _ ↦ measurable_fst]
    exact congrArg _ (funext fun i ↦ (h i).map_fst.symm)
  have hν : infinitePi ν = (infinitePi γ).map fun ω i ↦ (ω i).2 := by
    rw [infinitePi_map_pi γ (f := fun _ ↦ Prod.snd) fun _ ↦ measurable_snd]
    exact congrArg _ (funext fun i ↦ (h i).map_snd.symm)
  rw [hμ, hν]
  exact stochasticLE_map_of_ae_le (by fun_prop) (by fun_prop) <| ae_all_iff.mpr fun i ↦
    (measurePreserving_eval_infinitePi γ i).quasiMeasurePreserving.ae (h i).ae_le

end InfinitePi

end MeasureTheory.Measure
