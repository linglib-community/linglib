/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independent sets in real-valued form

The product rule of independent sets for real-valued masses, the form in which confirmation and
relevance measures compute. `[UPSTREAM]` candidates for
`Mathlib/Probability/Independence/Basic.lean`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t : Set Ω}

theorem IndepSet.measureReal_inter_eq_mul (h : IndepSet s t μ) :
    μ.real (s ∩ t) = μ.real s * μ.real t := by
  simp only [measureReal_def, h.measure_inter_eq_mul, ENNReal.toReal_mul]

theorem indepSet_iff_measureReal_inter_eq_mul [IsZeroOrProbabilityMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) : IndepSet s t μ ↔ μ.real (s ∩ t) = μ.real s * μ.real t := by
  rw [indepSet_iff_measure_inter_eq_mul hs ht μ, ← ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_mul]
  rfl

end ProbabilityTheory
