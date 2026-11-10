/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Dirac measures and their sums

A Dirac measure is a zero-one measure, and a measure concentrated at a point is a multiple of the
Dirac measure there. A nonzero measure on a countable space charges some point. The measure
`Measure.sum fun b ↦ w b • dirac b` gives a measurable set the total weight of its points.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/Dirac/Basic.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

section Dirac

variable {α : Type*} [MeasurableSpace α]

instance dirac.isZeroOneMeasure (a : α) : IsZeroOneMeasure (dirac a) :=
  ⟨fun _ _ ↦ dirac_apply_eq_zero_or_one⟩

/-- A nonzero measure on a countable space charges some point. -/
theorem exists_measure_singleton_ne_zero [Countable α] (μ : Measure α) [NeZero μ] :
    ∃ a, μ {a} ≠ 0 := by
  simpa [ext_iff_singleton] using NeZero.ne μ

variable [MeasurableSingletonClass α] {μ : Measure α} {a : α}

/-- A measure is concentrated at a point iff it is a multiple of the Dirac measure there. -/
theorem ae_eq_iff_eq_smul_dirac : (∀ᵐ x ∂μ, x = a) ↔ μ = μ {a} • dirac a := by
  simpa using ae_mem_finset_iff (μ := μ) (s := {a})

/-- A probability measure is concentrated at a point iff it is the Dirac measure there. -/
theorem ae_eq_iff_eq_dirac [IsProbabilityMeasure μ] : (∀ᵐ x ∂μ, x = a) ↔ μ = dirac a := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h1 : μ {a} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton a)).1 (ae_iff.1 h)
  rw [ae_eq_iff_eq_smul_dirac.1 h, h1, one_smul]

alias ⟨eq_dirac_of_ae_eq, _⟩ := ae_eq_iff_eq_dirac

end Dirac

section Sum

variable {β : Type*} [MeasurableSpace β]

/-- A sum of scaled Dirac measures gives a measurable set the total weight of its points. -/
theorem sum_smul_dirac_apply (w : β → ℝ≥0∞) {s : Set β} (hs : MeasurableSet s) :
    sum (fun b ↦ w b • dirac b) s = ∑' b, s.indicator w b := by
  rw [sum_apply _ hs]
  exact tsum_congr fun b ↦ by by_cases hb : b ∈ s <;> simp [dirac_apply' _ hs, hb]

/-- Nonnegative real weights on a finite type with sum one give a probability measure. -/
theorem isProbabilityMeasure_sum_ofReal_smul_dirac [Fintype β] {w : β → ℝ} (hw : ∀ b, 0 ≤ w b)
    (h : ∑ b, w b = 1) : IsProbabilityMeasure (sum fun b ↦ ENNReal.ofReal (w b) • dirac b) :=
  (h ▸ hasSum_fintype w).isProbabilityMeasure_sum_dirac hw

variable [MeasurableSingletonClass β]

theorem sum_smul_dirac_apply_finset (w : β → ℝ≥0∞) (s : Finset β) :
    sum (fun b ↦ w b • dirac b) ↑s = ∑ b ∈ s, w b := by
  rw [← sum_measure_singleton]
  simp only [sum_smul_dirac_singleton]

theorem sum_ofReal_smul_dirac_real_singleton {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (b : β) :
    (sum fun b ↦ ENNReal.ofReal (w b) • dirac b).real {b} = w b := by
  rw [measureReal_def, sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hw b)]

/-- With nonnegative real weights on a finite type, a set has the total weight of its points. -/
theorem sum_ofReal_smul_dirac_real_apply [Fintype β] {w : β → ℝ} (hw : ∀ b, 0 ≤ w b)
    (s : Set β) : (sum fun b ↦ ENNReal.ofReal (w b) • dirac b).real s = ∑ b, s.indicator w b := by
  rw [← s.toFinite.coe_toFinset, measureReal_def, sum_smul_dirac_apply_finset,
    ENNReal.toReal_sum fun _ _ ↦ ENNReal.ofReal_ne_top,
    Finset.sum_indicator_subset _ (Finset.subset_univ _)]
  simp only [ENNReal.toReal_ofReal (hw _)]

end Sum

end MeasureTheory.Measure
