/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.DropRight

/-!
# Lemmas about `List.rtake` and `List.rdrop`

`Mathlib/Data/List/DropRight.lean` defines `List.rtake l n` and `List.rdrop l n`, the last `n`
elements of `l` and `l` without them, and proves only their `nil`, `zero`, `concat`, and reverse
characterizations, plus a few `rdrop`-of-append facts. This file supplies the tail mirrors of the
`List.take` and `List.drop` API in `Init/Data/List/Nat/TakeDrop.lean`, each proved by reducing to
its front counterpart through `List.rtake_eq_reverse_take_reverse` or
`List.rdrop_eq_reverse_drop_reverse`. [UPSTREAM] candidates for `Mathlib/Data/List/DropRight.lean`.

## Main results

* `List.length_rtake`, `List.length_rtake_le`, `List.rtake_of_length_le`, and their `rdrop`
  twins `List.length_rdrop` and `List.rdrop_of_length_le`: lengths and saturation on a short
  list, mirroring `List.length_take`, `List.length_take_le`, `List.take_of_length_le`,
  `List.length_drop`, and `List.drop_of_length_le`.
* `List.getElem?_rtake`, `List.getElem?_rdrop`, `List.getLast?_rtake`: indexing into a tail-take
  or tail-drop, mirroring `List.getElem?_drop`, `List.getElem?_take`, and `List.head?_take`.
* `List.rtake_rtake`, `List.rtake_append`, `List.rdrop_append`: nested tail-takes and the
  tail-take or tail-drop of an append, mirroring `List.take_take`, `List.take_append`, and
  `List.drop_append`. `List.rtake_append_of_le_length`, `List.rtake_append_length`, and
  `List.rtake_append_length_add` are the corollaries mirroring `List.take_append_of_le_length`
  and mathlib's `List.rdrop_append_length` and `List.rdrop_append_length_add`.
* `List.rdrop_prefix`, `List.rtake_suffix`, `List.rdrop_append_rtake`: a tail-drop is a prefix, a
  tail-take a suffix, and together they recover the list, mirroring `List.take_prefix`,
  `List.drop_suffix`, and `List.take_append_drop`. `List.rtake_eq_iff` characterizes a tail-take
  as the suffix of its length, mirroring `List.suffix_iff_eq_drop`.
* `List.rtake_append_rtake` and `List.rtake_append_append_of_le_length`: the last `n` elements
  are a sufficient state, so truncating before appending, or prepending anything to a block of
  length at least `n`, leaves the tail-take unchanged.
-/

@[expose] public section

namespace List

variable {α : Type*} {l l₁ l₂ : List α} {m n : ℕ}

@[simp] theorem length_rtake : (l.rtake n).length = min n l.length := by
  simp [rtake_eq_reverse_take_reverse]

theorem length_rtake_le (n : ℕ) (l : List α) : (l.rtake n).length ≤ n :=
  length_rtake.trans_le (Nat.min_le_left ..)

@[simp] theorem length_rdrop : (l.rdrop n).length = l.length - n := by
  simp [rdrop_eq_reverse_drop_reverse]

theorem rtake_of_length_le (h : l.length ≤ n) : l.rtake n = l := by
  rw [rtake_eq_reverse_take_reverse, take_of_length_le (by rwa [length_reverse]), reverse_reverse]

theorem rdrop_of_length_le (h : l.length ≤ n) : l.rdrop n = [] := by
  simp [rdrop, Nat.sub_eq_zero_of_le h]

theorem getElem?_rtake {i : ℕ} : (l.rtake n)[i]? = l[l.length - n + i]? :=
  getElem?_drop

theorem getElem?_rdrop {i : ℕ} : (l.rdrop n)[i]? = if i < l.length - n then l[i]? else none := by
  rw [rdrop, getElem?_take]

theorem getLast?_rtake : (l.rtake n).getLast? = if n = 0 then none else l.getLast? := by
  rw [rtake_eq_reverse_take_reverse, getLast?_reverse, head?_take, head?_reverse]

theorem rtake_rtake : (l.rtake n).rtake m = l.rtake (min m n) := by
  simp [rtake_eq_reverse_take_reverse, take_take]

theorem rtake_append : (l₁ ++ l₂).rtake n = l₁.rtake (n - l₂.length) ++ l₂.rtake n := by
  simp [rtake_eq_reverse_take_reverse, take_append]

theorem rtake_append_of_le_length (h : n ≤ l₂.length) : (l₁ ++ l₂).rtake n = l₂.rtake n := by
  simp [rtake_append, Nat.sub_eq_zero_of_le h]

@[simp] theorem rtake_append_length : (l₁ ++ l₂).rtake l₂.length = l₂ := by
  simp [rtake_append, rtake_of_length_le]

@[simp] theorem rtake_append_length_add (k : ℕ) :
    (l₁ ++ l₂).rtake (l₂.length + k) = l₁.rtake k ++ l₂ := by
  simp [rtake_append, rtake_of_length_le]

theorem rdrop_append : (l₁ ++ l₂).rdrop n = l₁.rdrop (n - l₂.length) ++ l₂.rdrop n := by
  simp [rdrop_eq_reverse_drop_reverse, drop_append]

theorem rdrop_prefix (n : ℕ) (l : List α) : l.rdrop n <+: l := take_prefix _ _

theorem rtake_suffix (n : ℕ) (l : List α) : l.rtake n <:+ l := drop_suffix _ _

theorem rtake_eq_iff {u : List α} : l.rtake n = u ↔ u <:+ l ∧ u.length = min n l.length := by
  refine ⟨by rintro rfl; exact ⟨rtake_suffix n l, length_rtake⟩, fun ⟨h, hlen⟩ ↦ ?_⟩
  rw [suffix_iff_eq_drop.1 h, hlen, rtake]
  congr 1
  omega

@[simp] theorem rdrop_append_rtake (n : ℕ) (l : List α) : l.rdrop n ++ l.rtake n = l := by
  rw [rdrop_eq_reverse_drop_reverse, rtake_eq_reverse_take_reverse, ← reverse_append,
    take_append_drop, reverse_reverse]

theorem rtake_append_rtake (n : ℕ) (l₁ l₂ : List α) :
    (l₁.rtake n ++ l₂).rtake n = (l₁ ++ l₂).rtake n := by
  rw [rtake_append, rtake_append, rtake_rtake, Nat.min_eq_left (Nat.sub_le _ _)]

theorem rtake_append_append_of_le_length (a u y : List α) (h : n ≤ u.length) :
    (a ++ u ++ y).rtake n = (u ++ y).rtake n := by
  rw [rtake_append, rtake_append, rtake_append,
    Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.sub_le _ _) h), rtake_zero, nil_append]

end List
