/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Pow.NNReal
public import Linglib.Core.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Geometric means under a measure on a finite type

The geometric mean of a function `f` under a measure `μ` on a finite type is the product of the
values of `f`, each to the power of the mass of its atom. Under a probability measure it is the
exponential of the expected logarithm of `f`, so it is the value itself when `f` is constant on
the atoms of positive mass, and evaluation at a point under a point mass.

## Main definitions

* `MeasureTheory.Measure.geomMean`: the geometric mean `∏ a, f a ^ μ.real {a}`.

## Main results

* `MeasureTheory.Measure.geomMean_dirac`: under a point mass the mean is evaluation.
* `MeasureTheory.Measure.geomMean_prod`: under a product measure the mean is the iterated mean.
* `MeasureTheory.Measure.geomMean_of_forall_eq`: the mean of a function constant on the atoms of
  positive mass is that constant.
* `MeasureTheory.Measure.geomMean_eq_zero_iff`: the mean vanishes exactly when the function
  vanishes at an atom of positive mass.
* `MeasureTheory.Measure.geomMean_eq_ofReal_exp_sum_log`: the mean is the exponential of the
  expected logarithm.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [Fintype α] {μ : Measure α} {f g : α → ℝ≥0∞} {c : ℝ≥0∞}

/-- The geometric mean of a function on a finite type under a measure weights each value by the
mass of its atom. -/
noncomputable def geomMean (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∏ a, f a ^ μ.real {a}

theorem geomMean_mul (μ : Measure α) (f g : α → ℝ≥0∞) :
    μ.geomMean (fun a ↦ f a * g a) = μ.geomMean f * μ.geomMean g := by
  simp only [geomMean, ENNReal.mul_rpow_of_nonneg _ _ measureReal_nonneg, Finset.prod_mul_distrib]

theorem geomMean_rpow (μ : Measure α) (f : α → ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) :
    μ.geomMean (fun a ↦ f a ^ r) = μ.geomMean f ^ r := by
  simp only [geomMean, ← ENNReal.prod_rpow_of_nonneg hr, ← ENNReal.rpow_mul, mul_comm r]

theorem geomMean_mono (h : ∀ a, f a ≤ g a) : μ.geomMean f ≤ μ.geomMean g :=
  Finset.prod_le_prod fun a _ ↦ ENNReal.rpow_le_rpow (h a) measureReal_nonneg

theorem geomMean_congr (h : ∀ a, μ {a} ≠ 0 → f a = g a) : μ.geomMean f = μ.geomMean g :=
  Finset.prod_congr rfl fun a _ ↦ by
    rcases eq_or_ne (μ {a}) 0 with h0 | h0
    · rw [measureReal_def, h0, ENNReal.toReal_zero, ENNReal.rpow_zero, ENNReal.rpow_zero]
    · rw [h a h0]

theorem geomMean_ne_top (h : ∀ a, μ {a} ≠ 0 → f a ≠ ∞) : μ.geomMean f ≠ ∞ :=
  ENNReal.prod_ne_top fun a _ hf ↦ by
    rcases ENNReal.rpow_eq_top_iff.1 hf with ⟨-, hneg⟩ | ⟨hf, hpos⟩
    · exact measureReal_nonneg.not_gt hneg
    · refine h a (fun h0 ↦ ?_) hf
      rw [measureReal_def, h0, ENNReal.toReal_zero] at hpos
      exact lt_irrefl _ hpos

theorem geomMean_ne_zero (h : ∀ a, μ {a} ≠ 0 → f a ≠ 0) : μ.geomMean f ≠ 0 := fun h0 ↦ by
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h0
  rcases ENNReal.rpow_eq_zero_iff.1 ha with ⟨hf, hpos⟩ | ⟨-, hneg⟩
  · refine h a (fun hμ ↦ ?_) hf
    rw [measureReal_def, hμ, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  · exact measureReal_nonneg.not_gt hneg

/-- The geometric mean vanishes exactly when the function vanishes at an atom of positive
mass. -/
theorem geomMean_eq_zero_iff [IsFiniteMeasure μ] :
    μ.geomMean f = 0 ↔ ∃ a, μ {a} ≠ 0 ∧ f a = 0 := by
  refine ⟨fun h ↦ by_contra fun hne ↦ geomMean_ne_zero (fun a hμ hf ↦ hne ⟨a, hμ, hf⟩) h,
    fun ⟨a, hμ, ha⟩ ↦ Finset.prod_eq_zero (Finset.mem_univ a) ?_⟩
  rw [ha, measureReal_def, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hμ (measure_ne_top μ _))]

/-- The geometric mean is the exponential of the expected logarithm, for a function that is
positive and finite at the atoms of positive mass. -/
theorem geomMean_eq_ofReal_exp_sum_log (h0 : ∀ a, μ {a} ≠ 0 → f a ≠ 0)
    (htop : ∀ a, μ {a} ≠ 0 → f a ≠ ∞) :
    μ.geomMean f = ENNReal.ofReal (Real.exp (∑ a, μ.real {a} * Real.log (f a).toReal)) := by
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rcases eq_or_ne (μ.real {a}) 0 with h | h
  · simp [h]
  · have hμ : μ {a} ≠ 0 := fun h' ↦ h (by rw [measureReal_def, h', ENNReal.toReal_zero])
    have hpos : 0 < (f a).toReal := ENNReal.toReal_pos (h0 a hμ) (htop a hμ)
    rw [← ENNReal.ofReal_toReal (htop a hμ), ENNReal.ofReal_rpow_of_pos hpos,
      Real.rpow_def_of_pos hpos, ENNReal.toReal_ofReal hpos.le, mul_comm]

/-- Under a product measure the geometric mean is the mean over the first factor of the means over
the second. -/
theorem geomMean_prod {β : Type*} [MeasurableSpace β] [Fintype β] (μ : Measure α) (ν : Measure β)
    [SFinite ν] (f : α × β → ℝ≥0∞) :
    (μ.prod ν).geomMean f = μ.geomMean fun a ↦ ν.geomMean fun b ↦ f (a, b) := by
  simp only [geomMean, Fintype.prod_prod_type, ← Set.singleton_prod_singleton,
    measureReal_prod_prod, ← ENNReal.prod_rpow_of_nonneg measureReal_nonneg, ← ENNReal.rpow_mul,
    mul_comm]

variable [MeasurableSingletonClass α]

@[simp] theorem geomMean_const (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ≥0∞) :
    μ.geomMean (fun _ ↦ c) = c := by
  rw [geomMean, ← ENNReal.rpow_sum_of_nonneg c fun _ _ ↦ measureReal_nonneg,
    sum_measureReal_singleton_eq_one, ENNReal.rpow_one]

/-- The geometric mean under a probability measure of a function constant on the atoms of
positive mass is that constant. -/
theorem geomMean_of_forall_eq [IsProbabilityMeasure μ] (h : ∀ a, μ {a} ≠ 0 → f a = c) :
    μ.geomMean f = c :=
  (geomMean_congr h).trans (geomMean_const μ c)

/-- Under a point mass the geometric mean is evaluation at the point. -/
@[simp] theorem geomMean_dirac (a : α) (f : α → ℝ≥0∞) : (dirac a).geomMean f = f a :=
  geomMean_of_forall_eq fun a' ha' ↦ by
    rw [dirac_apply' a (measurableSet_singleton a')] at ha'
    rw [Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero ha')]

end MeasureTheory.Measure
