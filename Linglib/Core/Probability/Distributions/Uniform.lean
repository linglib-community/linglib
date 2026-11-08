/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Distributions.Uniform

/-!
# Two uniform measures on a finset

Mathlib has two uniform measures on finite data: `ProbabilityTheory.uniformOn s`, the counting
measure conditioned on a set, and `MeasureTheory.Measure.uniformOfFinset s`, the average of the
Dirac masses at the points of a finset. They agree on a finset.
-/

public section

open MeasureTheory
open scoped ENNReal Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- On a finset, the conditioned counting measure is the average of the Dirac masses. -/
theorem uniformOn_eq_uniformOfFinset (s : Finset Ω) :
    uniformOn (s : Set Ω) = Measure.uniformOfFinset s := by
  classical
  ext t -
  have : (s : Set Ω) ∩ t = ↑(s.filter (· ∈ t)) := by ext; simp
  rw [Measure.uniformOfFinset_apply, uniformOn, cond_apply s.measurableSet,
    Measure.count_apply_finset, this, Measure.count_apply_finset, ENNReal.div_eq_inv_mul]

end ProbabilityTheory
