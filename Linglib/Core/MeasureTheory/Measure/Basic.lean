/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Measures of ranges, and measures on `Option`

The measure of the range of an injective map out of a countable type is the sum of the measures of
the image points, and a measure on `Option α` is its mass at `none` plus its mass on the range of
`some`; an integral over `Option α` [splits the same way](##MeasureTheory.lintegral_option).
`[UPSTREAM]` candidates for `Mathlib/MeasureTheory/Measure/Basic.lean`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

theorem measure_range_eq_tsum [Countable β] [MeasurableSingletonClass α] {μ : Measure α}
    {f : β → α} (hf : Function.Injective f) : μ (range f) = ∑' b, μ {f b} := by
  rw [← iUnion_singleton_eq_range,
    measure_iUnion (fun _ _ h ↦ disjoint_singleton.2 (hf.ne h)) fun _ ↦ .singleton _]

theorem measure_singleton_none_add_measure_range_some (μ : Measure (Option α)) :
    μ {none} + μ (range some) = μ univ := by
  rw [← compl_range_some, add_comm, measure_add_measure_compl measurableSet_range_some]

/-- An integral over `Option α` is the term at `none` plus the sum of the terms at each
`some a`. -/
theorem lintegral_option [Countable α] [MeasurableSingletonClass α] (μ : Measure (Option α))
    (f : Option α → ℝ≥0∞) :
    ∫⁻ o, f o ∂μ = f none * μ {none} + ∑' a, f (some a) * μ {some a} := by
  have h : ∑' o : Option α, (if o = none then 0 else f o * μ {o}) =
      ∑' a, f (some a) * μ {some a} := by
    rw [← (Option.some_injective α).tsum_eq (f := fun o ↦ if o = none then 0 else f o * μ {o})]
    · simp
    · intro o ho
      cases o with
      | none => simp at ho
      | some a => exact mem_range_self a
  rw [lintegral_countable', ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  convert h

end MeasureTheory
