/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The lower Lebesgue integral against a sum of measures

The integral is additive in the measure, so it commutes with the sum of a list or of a multiset of
measures, as mathlib's `MeasureTheory.lintegral_finsetSum_measure` says for a sum over a finset.
`[UPSTREAM]`
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

@[simp]
theorem lintegral_multisetSum_measure (μs : Multiset (Measure α)) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μs.sum = (μs.map fun μ ↦ ∫⁻ a, f a ∂μ).sum :=
  let F : Measure α →+ ℝ≥0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_multiset_sum F μs

@[simp]
theorem lintegral_listSum_measure (μs : List (Measure α)) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μs.sum = (μs.map fun μ ↦ ∫⁻ a, f a ∂μ).sum :=
  mod_cast lintegral_multisetSum_measure (μs : Multiset (Measure α)) f

end MeasureTheory
