/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Topology.UnitInterval

/-!
# The unit interval in the extended nonnegative reals

A point of the unit interval and its reflection add up to one as extended nonnegative reals, the
form in which they weigh the two points of a Bernoulli measure.
-/

@[expose] public section

open scoped ENNReal unitInterval

namespace unitInterval

@[simp] theorem coe_toNNReal_add_coe_toNNReal_symm (x : I) :
    (toNNReal x : ℝ≥0∞) + toNNReal (σ x) = 1 := by
  rw [← ENNReal.coe_add, toNNReal_add_toNNReal_symm, ENNReal.coe_one]

@[simp] theorem coe_toNNReal_symm_add_coe_toNNReal (x : I) :
    (toNNReal (σ x) : ℝ≥0∞) + toNNReal x = 1 := by
  rw [← ENNReal.coe_add, toNNReal_symm_add_toNNReal, ENNReal.coe_one]

end unitInterval
