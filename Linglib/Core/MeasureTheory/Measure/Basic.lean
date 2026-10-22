/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Measures of ranges, and measures on `Option`

The measure of the range of an injective map out of a countable type is the sum of the measures of
the image points, and a measure on `Option α` is its mass at `none` plus its mass on the range of
`some`. `[UPSTREAM]` candidates for `Mathlib/MeasureTheory/Measure/Basic.lean`.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

theorem measure_range_eq_tsum [Countable β] [MeasurableSingletonClass α] {μ : Measure α}
    {f : β → α} (hf : Function.Injective f) : μ (range f) = ∑' b, μ {f b} := by
  rw [← iUnion_singleton_eq_range,
    measure_iUnion (fun _ _ h ↦ disjoint_singleton.2 (hf.ne h)) fun _ ↦ .singleton _]

theorem measure_singleton_none_add_measure_range_some (μ : Measure (Option α)) :
    μ {none} + μ (range some) = μ univ := by
  rw [← compl_range_some, add_comm, measure_add_measure_compl measurableSet_range_some]

end MeasureTheory
