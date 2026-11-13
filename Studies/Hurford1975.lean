/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Nat.Hyperoperation
public import Mathlib.Data.Set.Basic

/-!
# Hurford (1975): The Linguistic Theory of Numerals

This file formalizes the deep structures of Hurford's numeral grammar and their interpretation.
A NUMBER is *one* or a PHRASE, optionally followed by another NUMBER, and denotes the sum of its
parts. A PHRASE is a NUMBER followed by an M and denotes their product. An M is a lexical base
such as *ten*, or a NUMBER followed by an M, and denotes the second raised to the power of the
first, so that *hundred* is `[two ten]`. A digit is a tally of marks. The three rules of
interpretation are one operation at three depths:
[addition](##Number.value_phraseAnd_eq_hyperoperation),
[multiplication](##Phrase.value_mk_eq_hyperoperation) and
[exponentiation](##M.value_mk_eq_hyperoperation) are the hyperoperations of levels 1, 2 and 3.

## Implementation notes

A base is a row of any number of marks above one. The grammar over a language's digits and
multipliers that later work shares, with the Packing Strategy, is `Numeral.Number`.

## TODO

The map from these deep structures to `Numeral.Number`, taking a tally to a digit and an M to
its value, and the preservation of values along it, are not stated.

## References

* [hurford-1975]
-/

@[expose] public section

namespace Hurford1975

/-! ### The phrase-structure categories -/

mutual
/-- A NUMBER is *one* or a PHRASE, optionally followed by another NUMBER, rule (2a) of
[hurford-1975], p. 19. -/
inductive Number where
  /-- *one*, a single mark, is a NUMBER. -/
  | one : Number
  /-- *one* followed by a NUMBER is a NUMBER. -/
  | oneAnd (rest : Number) : Number
  /-- A PHRASE is a NUMBER. -/
  | phrase (p : Phrase) : Number
  /-- A PHRASE followed by a NUMBER is a NUMBER, as in *twenty-three*. -/
  | phraseAnd (p : Phrase) (rest : Number) : Number
  deriving DecidableEq, Repr

/-- A PHRASE is a NUMBER followed by an M, as in *two hundred*, rule (2b). -/
inductive Phrase where
  | mk (n : Number) (m : M) : Phrase
  deriving DecidableEq, Repr

/-- An M is a lexical base or a NUMBER followed by an M, as *hundred* is `[two ten]`, rule (2c). -/
inductive M where
  /-- A lexical base is a row of `b` marks, *ten* in English and 2, 5 or 20 in some other
  languages ([hurford-1975], p. 21). -/
  | base (b : ℕ) (hb : 1 < b := by decide) : M
  /-- A NUMBER followed by an M is an M. -/
  | mk (n : Number) (m : M) : M
  deriving DecidableEq, Repr
end

/-! ### The projection rules -/

mutual
/-- The value of a NUMBER is the sum of its immediate constituents, (23) of [hurford-1975],
pp. 29–30. -/
def Number.value : Number → ℕ
  | .one => 1
  | .oneAnd rest => 1 + rest.value
  | .phrase p => p.value
  | .phraseAnd p rest => p.value + rest.value

/-- The value of a PHRASE is the product of its immediate constituents. -/
def Phrase.value : Phrase → ℕ
  | .mk n m => n.value * m.value

/-- The value of an M is its second constituent raised to the power of its first. -/
def M.value : M → ℕ
  | .base b _ => b
  | .mk n m => m.value ^ n.value
end

/-- *ten* is the base of ten marks. -/
def M.ten : M := .base 10

@[simp] theorem M.value_ten : M.ten.value = 10 := rfl

/-! ### One operation at three levels

The single projection rule (29) of [hurford-1975], p. 34, values a node of depth `d` with
immediate constituents of values `x` and `y` as `CALCULATE+ d x y`, the depth being 1 at NUMBERs,
2 at PHRASEs and 3 at Ms by the convention (28). CALCULATE, (26) on p. 32, starts from `y` and
applies the operation of depth `d - 1` to it `x` times at depth 1 and `x - 1` times above, depth
0 being incrementing, so that for `x ≥ 1` it is `hyperoperation d y x`. Its fourth argument is
the sign `+`, which `-` replaces for the inverse operations. -/

/-- Addition at a NUMBER is the hyperoperation of level 1. -/
theorem Number.value_phraseAnd_eq_hyperoperation (p : Phrase) (rest : Number) :
    (phraseAnd p rest).value = hyperoperation 1 rest.value p.value := by
  rw [hyperoperation_one, value, add_comm]

/-- Multiplication at a PHRASE is the hyperoperation of level 2. -/
theorem Phrase.value_mk_eq_hyperoperation (n : Number) (m : M) :
    (mk n m).value = hyperoperation 2 m.value n.value := by
  rw [hyperoperation_two, value, mul_comm]

/-- Exponentiation at an M is the hyperoperation of level 3. -/
theorem M.value_mk_eq_hyperoperation (n : Number) (m : M) :
    (mk n m).value = hyperoperation 3 m.value n.value := by
  rw [hyperoperation_three, value]

/-! ### Values -/

theorem M.value_pos : ∀ m : M, 0 < m.value
  | .base _ hb => Nat.zero_lt_of_lt hb
  | .mk _ m => Nat.pow_pos m.value_pos

mutual
theorem Number.value_pos : ∀ n : Number, 0 < n.value
  | .one => Nat.one_pos
  | .oneAnd _ => Nat.add_pos_left Nat.one_pos _
  | .phrase p => p.value_pos
  | .phraseAnd p _ => Nat.add_pos_left p.value_pos _

theorem Phrase.value_pos : ∀ p : Phrase, 0 < p.value
  | .mk n m => Nat.mul_pos n.value_pos m.value_pos
end

theorem M.one_lt_value : ∀ m : M, 1 < m.value
  | .base _ hb => hb
  | .mk n m => m.one_lt_value.trans_le (Nat.le_self_pow n.value_pos.ne' _)

/-- `tally n` is the NUMBER `[one [one ... one]]` of `n + 1` marks, the structure of the digits
*one* to *nine* ([hurford-1975], p. 23). -/
def Number.tally : ℕ → Number
  | 0 => .one
  | n + 1 => .oneAnd (tally n)

@[simp] theorem Number.value_tally (n : ℕ) : (tally n).value = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tally, value, ih, add_comm]

theorem Number.range_value : Set.range value = {n | 0 < n} := by
  ext n
  refine ⟨fun ⟨e, he⟩ ↦ he ▸ e.value_pos, fun hn ↦ ⟨tally (n - 1), ?_⟩⟩
  simp only [value_tally]
  exact Nat.sub_add_cancel hn

/-- `tenPow k` is the M of value `10 ^ (k + 1)`, *ten* or `[k + 1 ten]`, *thousand* being
`[three ten]` ([hurford-1975], p. 23). -/
def M.tenPow : ℕ → M
  | 0 => .ten
  | k + 1 => .mk (.tally (k + 1)) .ten

@[simp] theorem M.value_tenPow (k : ℕ) : (tenPow k).value = 10 ^ (k + 1) := by
  cases k with
  | zero => rfl
  | succ k => simp [tenPow, value]

end Hurford1975
