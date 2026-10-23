/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The layer cake formula for functions into `ℕ`

Mathlib's layer cake formula, `MeasureTheory.lintegral_eq_lintegral_meas_lt`, integrates the
measures of the superlevel sets of a real function. For a function into `ℕ` the integral is a
sum: the integral of `f` is the sum over `n` of the measure of `{x | n < f x}`, the tail-sum
formula for the expectation of a random variable with values in `ℕ`. `[UPSTREAM]`

## Main results

* `MeasureTheory.lintegral_natCast_eq_tsum_measure_lt`: the tail-sum formula.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_natCast_eq_tsum_measure_lt {f : α → ℕ} (hf : Measurable f) :
    ∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑' n, μ {x | n < f x} := by
  have hm (n : ℕ) : MeasurableSet {x | n < f x} := hf measurableSet_Ioi
  have h (x : α) : (f x : ℝ≥0∞) = ∑' n : ℕ, {x | n < f x}.indicator 1 x := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [tsum_eq_sum (s := Finset.range (f x)) fun n hn ↦ ite_eq_right (by simpa using hn),
      Finset.sum_ite_of_true fun n hn ↦ Finset.mem_range.1 hn]
    simp
  simp_rw [h]
  rw [lintegral_tsum fun n ↦ (measurable_one.indicator (hm n)).aemeasurable]
  exact tsum_congr fun n ↦ lintegral_indicator_one (hm n)

end MeasureTheory
