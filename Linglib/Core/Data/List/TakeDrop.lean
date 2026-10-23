/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.TakeDrop

/-!
# Membership and extensionality for `take` and `drop` by index

The `getElem?` forms of `List.mem_take_iff_getElem` and `List.mem_drop_iff_getElem`: an
element of a prefix or suffix is an entry of the original list at an index on that side of
the cut. Two lists have the same `take n` exactly when they agree at every index below `n`
(`List.take_eq_take_iff_getElem?`), and the same `drop n` exactly when they agree from `n` on
(`List.drop_eq_drop_iff_getElem?`); the extensionality lemmas `List.ext_take_getElem?` and
`List.ext_drop_getElem?` are their reverse directions. Also `List.take_append_take`: truncating
the right operand before taking a prefix is a no-op. [UPSTREAM] candidates for
`Init/Data/List/Nat/TakeDrop.lean`, beside their `getElem` counterparts and `List.ext_getElem?`.
-/

@[expose] public section

namespace List

variable {α : Type*} {l l₁ l₂ : List α} {a : α} {n : ℕ}

theorem mem_take_iff_getElem? : a ∈ l.take n ↔ ∃ i < n, l[i]? = some a := by
  simp [mem_iff_getElem?, getElem?_take]

theorem mem_drop_iff_getElem? : a ∈ l.drop n ↔ ∃ i ≥ n, l[i]? = some a := by
  simp only [mem_iff_getElem?, getElem?_drop]
  exact ⟨fun ⟨i, h⟩ ↦ ⟨n + i, Nat.le_add_right n i, h⟩,
    fun ⟨i, hn, h⟩ ↦ ⟨i - n, by rwa [Nat.add_sub_cancel' hn]⟩⟩

theorem ext_take_getElem? (h : ∀ k < n, l₁[k]? = l₂[k]?) : l₁.take n = l₂.take n :=
  ext_getElem? fun k ↦ by
    rcases Nat.lt_or_ge k n with hk | hk
    · simpa only [getElem?_take_of_lt hk] using h k hk
    · simp [getElem?_take_eq_none hk]

theorem ext_drop_getElem? (h : ∀ k, n ≤ k → l₁[k]? = l₂[k]?) : l₁.drop n = l₂.drop n :=
  ext_getElem? fun k ↦ by simpa only [getElem?_drop] using h (n + k) (Nat.le_add_right n k)

theorem take_eq_take_iff_getElem? : l₁.take n = l₂.take n ↔ ∀ k < n, l₁[k]? = l₂[k]? :=
  ⟨fun h k hk ↦ by rw [← getElem?_take_of_lt hk, h, getElem?_take_of_lt hk], ext_take_getElem?⟩

theorem drop_eq_drop_iff_getElem? : l₁.drop n = l₂.drop n ↔ ∀ k, n ≤ k → l₁[k]? = l₂[k]? := by
  refine ⟨fun h k hk ↦ ?_, ext_drop_getElem?⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [← getElem?_drop, h, getElem?_drop]

theorem take_eq_take_of_le {m : ℕ} (h : l₁.take m = l₂.take m) (hnm : n ≤ m) :
    l₁.take n = l₂.take n := by
  rw [← Nat.min_eq_left hnm, ← take_take, h, take_take]

theorem drop_eq_drop_of_le {m : ℕ} (h : l₁.drop m = l₂.drop m) (hmn : m ≤ n) :
    l₁.drop n = l₂.drop n := by
  rw [← Nat.add_sub_cancel' hmn, ← drop_drop, h, drop_drop]

theorem take_append_take (n : ℕ) (l₁ l₂ : List α) :
    (l₁ ++ l₂.take n).take n = (l₁ ++ l₂).take n := by
  simp [take_append, take_take]

theorem lt_length_of_mem_drop (h : a ∈ l.drop n) : n < l.length :=
  Nat.not_le.mp (drop_eq_nil_iff.not.mp (ne_nil_of_mem h))

end List
