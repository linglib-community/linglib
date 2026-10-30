/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Dirac measures and their finite sums

A Dirac measure is a zero-one measure, and a probability measure almost surely equal to a point
is the Dirac measure at it. A nonzero measure on a countable space charges some point. On a finite
type with measurable singletons, `∑ b, w b • dirac b` gives a set the total weight of its points;
`Measure.ofWeights w` names it. With nonnegative real weights, `Measure.ofRealWeights w`, its real
values are sums of those weights, and it is a probability measure when they sum to one.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/Dirac.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

section PointMass

variable {α : Type*} [MeasurableSpace α]

instance (a : α) : IsZeroOneMeasure (dirac a) := ⟨fun _ _ ↦ dirac_apply_eq_zero_or_one⟩

theorem eq_dirac_of_ae_eq [MeasurableSingletonClass α] {μ : Measure α} [IsProbabilityMeasure μ]
    {a : α} (h : ∀ᵐ x ∂μ, x = a) : μ = dirac a := by
  have h0 : μ {a}ᶜ = 0 := by have := ae_iff.1 h; exact this
  ext s hs
  rw [dirac_apply' _ hs, ← measure_inter_add_sdiff s (measurableSet_singleton a),
    measure_mono_null (s := s \ {a}) (fun _ hx ↦ hx.2) h0, add_zero]
  by_cases has : a ∈ s
  · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 has), Set.indicator_of_mem has,
      Pi.one_apply, ← prob_compl_eq_zero_iff (measurableSet_singleton a), h0]
  · rw [Set.indicator_of_notMem has]
    exact measure_mono_null (fun x hx (hxa : x = a) ↦ has (hxa ▸ hx.1)) h0

/-- A nonzero measure on a countable space charges some point. -/
theorem exists_measure_singleton_ne_zero [Countable α] (μ : Measure α) [NeZero μ] :
    ∃ a, μ {a} ≠ 0 := by
  by_contra! h
  exact NeZero.ne μ (ext_of_singleton fun a ↦ by simp [h a])

end PointMass

variable {β : Type*} [MeasurableSpace β] [Fintype β] [MeasurableSingletonClass β]

theorem sum_smul_dirac_apply (w : β → ℝ≥0∞) (s : Set β) :
    (∑ b, w b • dirac b) s = ∑ b, s.indicator w b := by
  rw [finsetSum_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hb : b ∈ s <;> simp [hb]

theorem sum_smul_dirac_apply_singleton (w : β → ℝ≥0∞) (b : β) :
    (∑ b', w b' • dirac b') {b} = w b := by
  classical
  simp [sum_smul_dirac_apply, Set.indicator_apply]

theorem sum_ofReal_smul_dirac_real_apply {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (s : Set β) :
    (∑ b, ENNReal.ofReal (w b) • dirac b).real s = ∑ b, s.indicator w b := by
  rw [measureReal_def, sum_smul_dirac_apply, ENNReal.toReal_sum fun b _ ↦ by
    by_cases hb : b ∈ s <;> simp [hb]]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hb : b ∈ s <;> simp [hb, hw b]

theorem isProbabilityMeasure_sum_ofReal_smul_dirac {w : β → ℝ} (hw : ∀ b, 0 ≤ w b)
    (h : ∑ b, w b = 1) : IsProbabilityMeasure (∑ b, ENNReal.ofReal (w b) • dirac b) :=
  ⟨by rw [sum_smul_dirac_apply, Set.indicator_univ,
    ← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ hw b, h, ENNReal.ofReal_one]⟩

omit [MeasurableSingletonClass β] in
/-- The measure on a finite type giving each point its weight. -/
noncomputable def ofWeights (w : β → ℝ≥0∞) : Measure β := ∑ b, w b • dirac b

@[simp] theorem ofWeights_apply_singleton (w : β → ℝ≥0∞) (b : β) : ofWeights w {b} = w b :=
  sum_smul_dirac_apply_singleton w b

theorem ofWeights_apply_singleton_ne_zero {w : β → ℝ≥0∞} {b : β} (h : w b ≠ 0) :
    ofWeights w {b} ≠ 0 := by
  rwa [ofWeights_apply_singleton]

theorem ofWeights_apply_finset (w : β → ℝ≥0∞) (s : Finset β) :
    ofWeights w ↑s = ∑ b ∈ s, w b := by
  rw [← sum_measure_singleton]
  simp only [ofWeights_apply_singleton]

theorem isFiniteMeasure_ofWeights {w : β → ℝ≥0∞} (hw : ∀ b, w b ≠ ∞) :
    IsFiniteMeasure (ofWeights w) :=
  ⟨by rw [← Finset.coe_univ, ofWeights_apply_finset]; exact ENNReal.sum_lt_top.2 fun b _ ↦
    (hw b).lt_top⟩

instance (w : β → ℕ) : IsFiniteMeasure (ofWeights fun b ↦ (w b : ℝ≥0∞)) :=
  isFiniteMeasure_ofWeights fun _ ↦ ENNReal.natCast_ne_top _

theorem ofWeights_real_singleton (w : β → ℝ≥0∞) (b : β) :
    (ofWeights w).real {b} = (w b).toReal := by
  rw [measureReal_def, ofWeights_apply_singleton]

omit [MeasurableSingletonClass β] in
/-- The measure on a finite type giving each point its real weight, truncated at zero. -/
noncomputable def ofRealWeights (w : β → ℝ) : Measure β := ofWeights fun b ↦ ENNReal.ofReal (w b)

instance (w : β → ℝ) : IsFiniteMeasure (ofRealWeights w) :=
  isFiniteMeasure_ofWeights fun _ ↦ ENNReal.ofReal_ne_top

theorem ofRealWeights_real_singleton {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (b : β) :
    (ofRealWeights w).real {b} = w b := by
  rw [ofRealWeights, ofWeights_real_singleton, ENNReal.toReal_ofReal (hw b)]

theorem isProbabilityMeasure_ofRealWeights {w : β → ℝ} (hw : ∀ b, 0 ≤ w b) (h : ∑ b, w b = 1) :
    IsProbabilityMeasure (ofRealWeights w) :=
  isProbabilityMeasure_sum_ofReal_smul_dirac hw h

end MeasureTheory.Measure
