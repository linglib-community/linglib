/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Powers of extended nonnegative reals to a sum, and times exponentials

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

/-! ### Powers times exponentials -/

theorem ofReal_exp_ne_zero (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem rpow_ne_zero_of_ne_zero {x : ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (hx : x ≠ 0) : x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h ↦ hx h.1, fun h ↦ absurd hα (not_le.mpr h.2)⟩

theorem rpow_mul_ofReal_exp_ne_top {x : ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (hx : x ≠ ∞) (c : ℝ) :
    x ^ α * ENNReal.ofReal (Real.exp c) ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα hx) ENNReal.ofReal_ne_top

theorem rpow_mul_ofReal_exp_ne_zero {x : ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (hx : x ≠ 0) (c : ℝ) :
    x ^ α * ENNReal.ofReal (Real.exp c) ≠ 0 :=
  mul_ne_zero (rpow_ne_zero_of_ne_zero hα hx) (ofReal_exp_ne_zero c)

theorem toReal_rpow_mul_ofReal_exp {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ∞) (α c : ℝ) :
    (x ^ α * ENNReal.ofReal (Real.exp (-(α * c)))).toReal =
      Real.exp (α * (Real.log x.toReal - c)) := by
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.rpow_def_of_pos (ENNReal.toReal_pos hx0 hx),
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_add]
  congr 1; ring

end ENNReal
