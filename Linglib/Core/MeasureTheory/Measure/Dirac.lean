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
Dirac measure there. Inclusion of sets is comparison of their measures under every measure. A
nonzero measure on a countable space charges some point. The measure
`∑ b, w b • dirac b` on a finite type gives a set the total weight of its points.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/Dirac/Basic.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

section Dirac

variable {α : Type*} [MeasurableSpace α]

instance dirac.isZeroOneMeasure (a : α) : IsZeroOneMeasure (dirac a) :=
  ⟨fun _ _ ↦ dirac_apply_eq_zero_or_one⟩

/-- One set is included in another exactly when it has at most its measure under every
measure. -/
theorem _root_.MeasureTheory.subset_iff_forall_measure_le [MeasurableSingletonClass α]
    {s t : Set α} : s ⊆ t ↔ ∀ μ : Measure α, μ s ≤ μ t := by
  refine ⟨fun h μ ↦ measure_mono h, fun h a ha ↦ by_contra fun hat ↦ ?_⟩
  simpa [dirac_apply, ha, hat] using h (dirac a)

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

section FinsetSum

variable {β : Type*} [MeasurableSpace β] [Fintype β]

/-- Nonnegative real weights on a finite type with sum one give a probability measure. -/
theorem isProbabilityMeasure_finsetSum_ofReal_smul_dirac {w : β → ℝ} (hw : ∀ b, 0 ≤ w b)
    (h : ∑ b, w b = 1) : IsProbabilityMeasure (∑ b, ENNReal.ofReal (w b) • dirac b) :=
  ⟨by simp [← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ hw b, h]⟩

variable [MeasurableSingletonClass β]

/-- A finite sum of scaled Dirac measures gives a set the total weight of its points. -/
theorem finsetSum_smul_dirac_apply (w : β → ℝ≥0∞) (s : Set β) :
    (∑ b, w b • dirac b) s = ∑ b, s.indicator w b := by
  rw [finsetSum_apply]
  exact Finset.sum_congr rfl fun b _ ↦ by by_cases hb : b ∈ s <;> simp [hb]

/-- A finite sum of scaled Dirac measures gives a point its weight. -/
theorem finsetSum_smul_dirac_singleton {w : β → ℝ≥0∞} {a : β} :
    (∑ b, w b • dirac b) {a} = w a := by
  classical
  simp [finsetSum_smul_dirac_apply, Set.indicator_apply]

theorem finsetSum_smul_dirac_apply_finset (w : β → ℝ≥0∞) (s : Finset β) :
    (∑ b, w b • dirac b) ↑s = ∑ b ∈ s, w b := by
  rw [← sum_measure_singleton]
  simp only [finsetSum_smul_dirac_singleton]

theorem finsetSum_ofReal_smul_dirac_real_singleton {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (b : β) :
    (∑ b, ENNReal.ofReal (w b) • dirac b).real {b} = w b := by
  rw [measureReal_def, finsetSum_smul_dirac_singleton, ENNReal.toReal_ofReal (hw b)]

/-- With nonnegative real weights, a set has the total weight of its points. -/
theorem finsetSum_ofReal_smul_dirac_real_apply {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (s : Set β) :
    (∑ b, ENNReal.ofReal (w b) • dirac b).real s = ∑ b, s.indicator w b := by
  rw [measureReal_def, finsetSum_smul_dirac_apply, ENNReal.toReal_sum fun b _ ↦ by
    by_cases hb : b ∈ s <;> simp [hb]]
  exact Finset.sum_congr rfl fun b _ ↦ by by_cases hb : b ∈ s <;> simp [hb, hw b]

end FinsetSum

end MeasureTheory.Measure
