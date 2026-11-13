/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Infixes of a three-part concatenation, and common prefixes

[An infix of `u ++ m ++ v` at most one longer than `m` lies in `u ++ m` or in
`m ++ v`](##infix_append_append_iff): this is the fact about short windows behind pumping arguments,
where `m` is a block of the pumped word that separates two others, and behind suffix substitution
in strictly local languages, where `m` is the shared `k - 1` letters.

The longest common prefix `List.commonPrefix l₁ l₂`, the greatest list that is a prefix of both,
is the meet of the prefix order.

## Implementation notes

Each declaration fills a gap. Neither core, Batteries nor mathlib defines a longest common prefix
of lists, and mathlib's `RootedTree` takes its meet as a `SemilatticeInf` instance rather than
deriving it, so `List.commonPrefix` is an [UPSTREAM] candidate for Batteries beside
`List.inits`. The short-window lemma refines core's `List.infix_append_iff`, which leaves the
overlap with `m` to the caller.
-/

@[expose] public section

namespace List

variable {α : Type*} {l u m v : List α} {x y : α}

/-- An infix of `u ++ m ++ v` at most one longer than `m` lies in `u ++ m` or in `m ++ v`. -/
theorem infix_append_append_iff (hl : l.length ≤ m.length + 1) :
    l <:+: u ++ m ++ v ↔ l <:+: u ++ m ∨ l <:+: m ++ v := by
  refine ⟨fun ⟨s, t, h⟩ ↦ ?_, ?_⟩
  · have hlen := congrArg length h
    simp only [length_append] at hlen
    rcases le_or_gt (s.length + l.length) (u.length + m.length) with hle | hle
    · exact .inl ((suffix_append s l).isInfix.trans (prefix_of_prefix_length_le ⟨t, h⟩
        (prefix_append _ _) (by simpa)).isInfix)
    · exact .inr ((prefix_append l t).isInfix.trans (suffix_of_suffix_length_le
        ⟨s, by simpa [append_assoc] using h⟩ ⟨u, by simp⟩
        (by simp only [length_append]; omega)).isInfix)
  · rintro (h | h)
    · exact h.trans (prefix_append _ _).isInfix
    · exact h.trans ⟨u, [], by simp [append_assoc]⟩

/-- An infix of `u ++ m ++ v` no longer than `m` misses an element that occurs only in `u` or an
element that occurs only in `v`. -/
theorem IsInfix.notMem_or_notMem_of_length_le (hl : l <:+: u ++ m ++ v)
    (hlen : l.length ≤ m.length) (hx : x ∉ m ++ v) (hy : y ∉ u ++ m) : x ∉ l ∨ y ∉ l :=
  ((infix_append_append_iff (by omega)).1 hl).symm.imp
    (fun h hx' ↦ hx (h.subset hx')) fun h hy' ↦ hy (h.subset hy')

/-- An infix of at most `k` elements of a list of at least `k` lies in an infix of exactly `k`. -/
theorem exists_infix_length_eq {s w : List α} {k : ℕ} (h : s <:+: w) (hs : s.length ≤ k)
    (hk : k ≤ w.length) : ∃ f, f <:+: w ∧ f.length = k ∧ s <:+: f := by
  obtain ⟨t, ht, hget⟩ := infix_iff_getElem?.1 h
  refine ⟨(w.drop (min t (w.length - k))).take k,
    (take_prefix _ _).isInfix.trans (drop_suffix _ _).isInfix, by simp; omega,
    infix_iff_getElem?.2 ⟨t - min t (w.length - k), by simp; omega, fun i hi ↦ ?_⟩⟩
  rw [getElem?_take_of_lt (by omega), getElem?_drop, ← hget i hi]
  congr 1
  omega

section DecidableEq

variable [DecidableEq α]

/-- `commonPrefix l₁ l₂` is the longest common prefix of `l₁` and `l₂`. -/
def commonPrefix : List α → List α → List α
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

theorem commonPrefix_prefix_left : ∀ l₁ l₂ : List α, commonPrefix l₁ l₂ <+: l₁
  | [], _ | _ :: _, [] => by simp [commonPrefix]
  | a :: as, b :: bs => by
    by_cases h : a = b
    · simpa [commonPrefix, h] using commonPrefix_prefix_left as bs
    · simp [commonPrefix, h]

theorem commonPrefix_prefix_right : ∀ l₁ l₂ : List α, commonPrefix l₁ l₂ <+: l₂
  | [], _ | _ :: _, [] => by simp [commonPrefix]
  | a :: as, b :: bs => by
    by_cases h : a = b
    · subst h
      simpa [commonPrefix] using commonPrefix_prefix_right as bs
    · simp [commonPrefix, h]

theorem prefix_commonPrefix : ∀ {r l₁ l₂ : List α}, r <+: l₁ → r <+: l₂ → r <+: commonPrefix l₁ l₂
  | [], _, _, _, _ => nil_prefix
  | _ :: rs, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by
    simpa [commonPrefix] using prefix_commonPrefix (r := rs) (prefix_append _ _) (prefix_append _ _)

end DecidableEq

end List
