/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The rising factorial as a ratio of real Gamma values

Away from the nonpositive integers, `Γ(x + n) / Γ(x)` is the rising factorial `(x)ₙ`, the real
counterpart of mathlib's `Complex.Gamma_add_nat_div_Gamma_eq`.

[UPSTREAM] candidate for `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`.
-/

@[expose] public section

namespace Real

/-- The ascending Pochhammer symbol is given by the ratio of `Γ` functions. -/
theorem Gamma_add_nat_div_Gamma_eq {n : ℕ} (x : ℝ) (hx : ∀ k : ℕ, x ≠ -k) :
    Gamma (x + n) / Gamma x = (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp [Gamma_ne_zero hx]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one fun h ↦ hx n (eq_neg_of_add_eq_zero_left h),
      ascPochhammer_succ_eval, ← ih]
    ring

end Real
