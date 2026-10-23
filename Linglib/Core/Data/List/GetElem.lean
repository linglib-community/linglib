/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Int.Notation
public import Linglib.Core.Data.List.TakeDrop

/-!
# Integer indexing into lists

`w[i]?` for `i : ℤ`: the entry of `w` at `i` when `0 ≤ i < w.length`, and `none` otherwise. This
is the `GetElem?` instance a list has as a two-sided family padded with blanks, so position
arithmetic across the left edge is ordinary `ℤ` arithmetic rather than a case split on `ℕ`
subtraction. The instance is lawful, so the generic `getElem?_pos`, `getElem?_neg`, and
`getElem?_eq_some_iff` apply; the lemmas here bridge to the `ℕ` index.

## Main results

* `List.getElem?_int_of_nonneg`, `List.getElem?_int_of_neg`, `List.getElem?_natCast`: the two
  cases of the instance and the `ℕ` specialization.
* `List.getElem?_int_eq_none_iff`: an entry is blank exactly outside `[0, w.length)`.
* `List.ext_getElem?_int` and `List.ext_take_getElem?_int`: extensionality for a list and its
  prefixes from agreement of integer-indexed entries.
* `List.getElem?_int_append_left` and `List.getElem?_int_take_of_lt`: the integer mirrors of
  `List.getElem?_append_left` and `List.getElem?_take_of_lt`.
-/

@[expose] public section

namespace List

variable {α : Type*} {w y u v : List α} {i : ℤ} {n : ℕ}

instance instGetElem?Int : GetElem? (List α) ℤ α fun w i ↦ 0 ≤ i ∧ i < w.length where
  getElem w i h := w[i.toNat]'(by omega)
  getElem? w i := if 0 ≤ i then w[i.toNat]? else none

instance : LawfulGetElem (List α) ℤ α fun w i ↦ 0 ≤ i ∧ i < w.length where
  getElem?_def w i _ := by
    show (if 0 ≤ i then w[i.toNat]? else none) = _
    split_ifs with h1 h2 h2
    · exact getElem?_eq_getElem (by omega)
    · exact getElem?_eq_none (by omega)
    · exact absurd h2.1 h1
    · rfl

theorem getElem_int (h : 0 ≤ i ∧ i < w.length) : w[i] = w[i.toNat]'(by omega) := rfl

theorem getElem?_int : w[i]? = if 0 ≤ i then w[i.toNat]? else none := rfl

theorem getElem?_int_of_nonneg (h : 0 ≤ i) : w[i]? = w[i.toNat]? := ite_eq_left h

theorem getElem?_int_of_neg (h : i < 0) : w[i]? = none := ite_eq_right (by omega)

@[simp] theorem getElem?_natCast (w : List α) (n : ℕ) : w[(n : ℤ)]? = w[n]? := by
  simp [getElem?_int]

@[simp] theorem getElem?_int_nil : ([] : List α)[i]? = none := by simp

theorem getElem?_int_eq_none_iff : w[i]? = none ↔ i < 0 ∨ (w.length : ℤ) ≤ i := by
  rw [_root_.getElem?_eq_none_iff]
  omega

/-- Agreement of integer-indexed entries up to the length of `w` forces equality. -/
theorem ext_getElem?_int (h : ∀ j : ℤ, j ≤ (w.length : ℤ) → y[j]? = w[j]?) : y = w := by
  have hy : y.length ≤ w.length := by
    have h1 := h (w.length : ℤ) (Int.le_refl _)
    rwa [getElem?_natCast, getElem?_natCast, getElem?_eq_none (Nat.le_refl _),
      getElem?_eq_none_iff] at h1
  refine ext_getElem? fun n ↦ ?_
  rcases Nat.lt_or_ge n w.length with hn | hn
  · simpa using h n (by omega)
  · rw [getElem?_eq_none hn, getElem?_eq_none (by omega)]

/-- Agreement of integer-indexed entries below `c` transfers prefixes of length `c`. -/
theorem ext_take_getElem?_int {c : ℕ} (h : ∀ j : ℤ, j < (c : ℤ) → y[j]? = w[j]?) :
    y.take c = w.take c :=
  ext_take_getElem? fun n hn ↦ by simpa using h n (by omega)

theorem getElem?_int_append_left (h : i < (u.length : ℤ)) : (u ++ v)[i]? = u[i]? := by
  by_cases h0 : 0 ≤ i
  · rw [getElem?_int_of_nonneg h0, getElem?_int_of_nonneg h0, getElem?_append_left (by omega)]
  · rw [getElem?_int_of_neg (by omega), getElem?_int_of_neg (by omega)]

theorem getElem?_int_take_of_lt {c : ℕ} (h : i < (c : ℤ)) : (w.take c)[i]? = w[i]? := by
  by_cases h0 : 0 ≤ i
  · rw [getElem?_int_of_nonneg h0, getElem?_int_of_nonneg h0, getElem?_take_of_lt (by omega)]
  · rw [getElem?_int_of_neg (by omega), getElem?_int_of_neg (by omega)]

end List
