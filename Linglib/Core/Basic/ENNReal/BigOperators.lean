/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Inv

/-!
# Products in `ℝ≥0∞`

Two finite products with one dominated by the other termwise, the larger having nonzero finite
factors, [are equal only when the factors are](##ENNReal.prod_eq_prod_iff_of_le). Multiplication
in `ℝ≥0∞` is not cancellative, so this is not an instance of `Finset.prod_eq_prod_iff_of_le`.

## Implementation notes

`[UPSTREAM]` candidate for `Mathlib/Basic/ENNReal/BigOperators.lean`.
-/

public section

open scoped ENNReal

namespace ENNReal

variable {ι : Type*} {s : Finset ι} {f g : ι → ℝ≥0∞}

theorem prod_eq_prod_iff_of_le (hle : ∀ i ∈ s, f i ≤ g i) (h0 : ∀ i ∈ s, g i ≠ 0)
    (htop : ∀ i ∈ s, g i ≠ ∞) : ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  refine ⟨fun h i hi ↦ ?_, Finset.prod_congr rfl⟩
  have key : (∏ j ∈ s, f j / g j) * ∏ j ∈ s, g j = ∏ j ∈ s, g j := by
    rw [← Finset.prod_mul_distrib, ← h]
    exact Finset.prod_congr rfl fun j hj ↦ ENNReal.div_mul_cancel (h0 j hj) (htop j hj)
  rw [ENNReal.mul_eq_right (Finset.prod_ne_zero_iff.mpr h0) (prod_ne_top htop)] at key
  exact (div_eq_one_iff (h0 i hi) (htop i hi)).mp <|
    (Finset.prod_eq_one_iff_of_le_one fun j hj ↦
      div_le_of_le_mul (by simpa using hle j hj)).mp key i hi

end ENNReal
