/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Rounding to the nearest multiple

Mirror of `Mathlib/Algebra/Order/Round.lean`: the additions a PR there would make. [UPSTREAM]

Rounding to the nearest multiple of `ε` sends `d` to `round (d / ε) • ε`. Mathlib bounds
`x - round x` and shows `round x` is the nearest integer; this file transfers both facts to
multiples of `ε`, and shows that `round` of a quotient by an odd natural factors through `round`.

## Main results

* `abs_sub_round_div_zsmul_le`: rounding to the nearest multiple of `ε` moves a point by at
  most `ε / 2`.
* `abs_sub_round_div_zsmul_le_abs_sub_zsmul`: no multiple of `ε` is nearer.
* `abs_sub_round_eq_half_iff`: the points moved by exactly a half are the half-integers.
* `round_div_two_mul_add_one`: `round (x / (2 * j + 1))` is `(round x + j) / (2 * j + 1)`.
-/

@[expose] public section

variable {α : Type*} [Field α] {ε : α}

private theorem sub_zsmul_eq_sub_mul (hε : ε ≠ 0) (d : α) (n : ℤ) :
    d - n • ε = (d / ε - n) * ε := by
  rw [zsmul_eq_mul, sub_mul, div_mul_cancel₀ d hε]

variable [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/-- Rounding to the nearest multiple of `ε` moves a point by at most `ε / 2`, the sibling of
`abs_sub_round` for multiples. -/
theorem abs_sub_round_div_zsmul_le (hε : 0 < ε) (d : α) :
    |d - round (d / ε) • ε| ≤ ε / 2 := by
  rw [sub_zsmul_eq_sub_mul hε.ne', abs_mul, abs_of_pos hε]
  exact (mul_le_mul_of_nonneg_right (abs_sub_round _) hε.le).trans_eq (by ring)

/-- The nearest multiple of `ε` is no farther from `d` than any multiple, the sibling of
`round_le` for multiples. -/
theorem abs_sub_round_div_zsmul_le_abs_sub_zsmul (hε : ε ≠ 0) (d : α) (n : ℤ) :
    |d - round (d / ε) • ε| ≤ |d - n • ε| := by
  rw [sub_zsmul_eq_sub_mul hε, sub_zsmul_eq_sub_mul hε, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (round_le (d / ε) n) (abs_nonneg ε)

/-- Rounding moves a point by exactly a half at the half-integers, the equality case of
`abs_sub_round`. -/
theorem abs_sub_round_eq_half_iff {x : α} : |x - round x| = 1 / 2 ↔ ∃ k : ℤ, x = k + 1 / 2 := by
  rw [round_eq]
  have h0 := Int.fract_nonneg (x + 1 / 2)
  have h1 := Int.fract_lt_one (x + 1 / 2)
  have hx : x - ⌊x + 1 / 2⌋ = Int.fract (x + 1 / 2) - 1 / 2 := by rw [Int.fract]; ring
  rw [hx]
  constructor
  · intro h
    have hf : Int.fract (x + 1 / 2) = 0 := by
      rcases abs_eq (by norm_num : (0 : α) ≤ 1 / 2) |>.1 h with h | h <;> linarith
    refine ⟨⌊x + 1 / 2⌋ - 1, ?_⟩
    rw [Int.fract, sub_eq_zero] at hf
    push_cast
    linarith
  · rintro ⟨k, rfl⟩
    rw [show (k : α) + 1 / 2 + 1 / 2 = ((k + 1 : ℤ) : α) by push_cast; ring, Int.fract_intCast]
    norm_num [abs_of_neg]

/-- Rounding a quotient by an odd natural factors through rounding, since the half-integers
`k * (2 * j + 1) + j + 1 / 2` at which `round (x / (2 * j + 1))` jumps are among those at which
`round x` jumps. -/
theorem round_div_two_mul_add_one (x : α) (j : ℕ) :
    round (x / (2 * j + 1 : ℕ)) = (round x + j) / (2 * j + 1 : ℕ) := by
  have hk : (0 : α) < (2 * j + 1 : ℕ) := by positivity
  rw [round_eq, round_eq, ← Int.floor_add_natCast, ← Int.floor_div_natCast]
  congr 1
  field_simp
  push_cast
  ring
