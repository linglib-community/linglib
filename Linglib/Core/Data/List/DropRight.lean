/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.DropRight

/-!
# Lemmas about `List.rtake` and `List.rdrop`

`Mathlib/Data/List/DropRight.lean` defines `l.rtake n` and `l.rdrop n`, the last `n` elements of
`l` and `l` without them. This file mirrors at the tail the API of `List.take` and `List.drop` in
`Init/Data/List/`. Reversal [exchanges](##List.rtake_reverse) `l.rtake n` and `l.take n`, and
`l.rtake n` is [the longest suffix of `l` of length at most `n`](##List.suffix_rtake_iff).
[UPSTREAM] candidates for `Mathlib/Data/List/DropRight.lean`.
-/

public section

namespace List

variable {α : Type*} {l l₁ l₂ : List α} {m n : ℕ}

/-! ### Lengths and short lists -/

@[simp] theorem length_rtake : (l.rtake n).length = min n l.length := by
  simp [rtake_eq_reverse_take_reverse]

theorem length_rtake_le (l : List α) (n : ℕ) : (l.rtake n).length ≤ n :=
  length_rtake.trans_le (Nat.min_le_left ..)

@[simp] theorem length_rdrop : (l.rdrop n).length = l.length - n := by
  simp [rdrop]

theorem rtake_of_length_le (h : l.length ≤ n) : l.rtake n = l := by
  simp [rtake, Nat.sub_eq_zero_of_le h]

theorem rdrop_of_length_le (h : l.length ≤ n) : l.rdrop n = [] := by
  simp [rdrop, Nat.sub_eq_zero_of_le h]

@[simp] theorem rtake_replicate {a : α} : (replicate m a).rtake n = replicate (min n m) a := by
  simp [rtake_eq_reverse_take_reverse]

/-! ### Reversal -/

theorem reverse_rtake : (l.rtake n).reverse = l.reverse.take n :=
  take_reverse.symm

theorem rtake_reverse : l.reverse.rtake n = (l.take n).reverse := by
  rw [rtake_eq_reverse_take_reverse, reverse_reverse]

/-! ### Elements -/

theorem getElem?_rtake {i : ℕ} : (l.rtake n)[i]? = l[l.length - n + i]? :=
  getElem?_drop

theorem getLast?_rtake : (l.rtake n).getLast? = if n = 0 then none else l.getLast? := by
  rw [rtake_eq_reverse_take_reverse, getLast?_reverse, head?_take, head?_reverse]

/-! ### Appending -/

theorem rtake_rtake : (l.rtake n).rtake m = l.rtake (min m n) := by
  simp [rtake_eq_reverse_take_reverse, take_take]

theorem rtake_append : (l₁ ++ l₂).rtake n = l₁.rtake (n - l₂.length) ++ l₂.rtake n := by
  simp [rtake_eq_reverse_take_reverse, take_append]

theorem rtake_append_of_le_length (h : n ≤ l₂.length) : (l₁ ++ l₂).rtake n = l₂.rtake n := by
  simp [rtake_append, Nat.sub_eq_zero_of_le h]

/-- Truncating `l₁` to its last `n` elements does not change the last `n` elements of
`l₁ ++ l₂`. -/
theorem rtake_rtake_append : (l₁.rtake n ++ l₂).rtake n = (l₁ ++ l₂).rtake n := by
  simp [rtake_append, rtake_rtake]

theorem rtake_cons_of_length_eq {a : α} (h : l.length = n) : (a :: l).rtake n = l := by
  simp [rtake, ← h]

theorem rdrop_cons_of_length_eq {a : α} (h : l.length = n) : (a :: l).rdrop n = [a] := by
  simp [rdrop, ← h]

theorem rdrop_append : (l₁ ++ l₂).rdrop n = l₁.rdrop (n - l₂.length) ++ l₂.rdrop n := by
  simp [rdrop_eq_reverse_drop_reverse, drop_append]

/-! ### Prefixes and suffixes -/

theorem rdrop_prefix (l : List α) (n : ℕ) : l.rdrop n <+: l := take_prefix _ _

theorem rtake_suffix (l : List α) (n : ℕ) : l.rtake n <:+ l := drop_suffix _ _

@[simp] theorem rdrop_append_rtake (l : List α) (n : ℕ) : l.rdrop n ++ l.rtake n = l :=
  take_append_drop _ _

/-- `l.rtake n` is the longest suffix of `l` of length at most `n`, mirroring
`List.prefix_take_iff`. -/
theorem suffix_rtake_iff {s : List α} : s <:+ l.rtake n ↔ s <:+ l ∧ s.length ≤ n := by
  rw [← reverse_prefix, reverse_rtake, prefix_take_iff, reverse_prefix, length_reverse]

/-- `l.rtake n` is the suffix of `l` of length `min n l.length`. -/
theorem rtake_eq_iff {u : List α} : l.rtake n = u ↔ u <:+ l ∧ u.length = min n l.length :=
  ⟨fun h ↦ h ▸ ⟨rtake_suffix l n, length_rtake⟩, fun ⟨h, hlen⟩ ↦
    ((suffix_rtake_iff.2 ⟨h, hlen.trans_le (Nat.min_le_left ..)⟩).eq_of_length
      (by simp [hlen])).symm⟩

end List
