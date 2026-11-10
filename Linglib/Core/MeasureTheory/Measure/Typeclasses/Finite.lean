/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Finite measures scaled by finite constants

A finite measure scaled by a natural number or by `ENNReal.ofReal r` is finite, as an instance,
beside mathlib's instance for scaling by an `ℝ≥0`.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

instance smul_ofReal_finite (r : ℝ) : IsFiniteMeasure (ENNReal.ofReal r • μ) :=
  μ.smul_finite ENNReal.ofReal_ne_top

instance smul_natCast_finite (n : ℕ) : IsFiniteMeasure ((n : ℝ≥0∞) • μ) :=
  μ.smul_finite (ENNReal.natCast_ne_top n)

end MeasureTheory.Measure
