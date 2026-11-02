/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Atoms of a probability measure on a finite type

On a finite type with measurable singletons, the real masses of the atoms of a probability
measure sum to one. `[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/Real.lean`.
-/

public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

theorem sum_measureReal_singleton_eq_one (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ a, μ.real {a} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

end MeasureTheory
