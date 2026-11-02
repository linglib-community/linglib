/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Powers of extended nonnegative reals to a sum

A power of an extended nonnegative real to a sum of nonnegative exponents is the product of the
powers, as for the reals.

`[UPSTREAM]` candidate for `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`, beside
`ENNReal.prod_rpow_of_nonneg`.
-/

public section

open scoped ENNReal

namespace ENNReal

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ}

theorem rpow_sum_of_nonneg (x : ℝ≥0∞) (hw : ∀ i ∈ s, 0 ≤ w i) :
    x ^ ∑ i ∈ s, w i = ∏ i ∈ s, x ^ w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      rpow_add_of_nonneg _ _ (hw i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)]

end ENNReal
