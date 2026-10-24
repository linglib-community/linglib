/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Short infixes of a three-part concatenation, and common prefixes

An infix of `u ++ m ++ v` no longer than `m` cannot contain both an element that occurs only in
`u` and an element that occurs only in `v`: this is the fact about short windows that pumping
arguments use, when `m` is a block of the pumped word that separates two others.

The longest common prefix `List.commonPrefix l₁ l₂`, the greatest list that is a prefix of both,
is the meet of the prefix order.

## Main definitions

* `List.commonPrefix`: the longest common prefix of two lists.

## Main results

* `List.IsInfix.notMem_or_notMem_of_length_le`: an infix of `u ++ m ++ v` no longer than `m` misses
  every element occurring only in `u` or every element occurring only in `v`.

## Implementation notes

Each declaration fills a gap. Neither core, Batteries nor mathlib defines a longest common prefix
of lists, and mathlib's `RootedTree` takes its meet as a `SemilatticeInf` instance rather than
deriving it, so `List.commonPrefix` is an [UPSTREAM] candidate for Batteries beside
`List.inits`. The short-window lemma, proved from core's `List.infix_append_iff`, would go up only
with a pumping lemma for context-free languages, which mathlib lacks.
-/

@[expose] public section

namespace List

variable {α : Type*} {l u m v : List α} {x y : α}

/-- An infix of `u ++ m ++ v` no longer than `m` misses an element that occurs only in `u` or an
element that occurs only in `v`. -/
theorem IsInfix.notMem_or_notMem_of_length_le (hl : l <:+: u ++ m ++ v)
    (hlen : l.length ≤ m.length) (hx : x ∉ m ++ v) (hy : y ∉ u ++ m) : x ∉ l ∨ y ∉ l := by
  rcases infix_append_iff.1 hl with h | h | ⟨l₁, l₂, rfl, h₁, h₂⟩
  · exact .inr fun hy' ↦ hy (h.subset hy')
  · exact .inl fun hx' ↦ hx (mem_append_right m (h.subset hx'))
  · refine .inl fun hx' ↦ hx ?_
    rw [length_append] at hlen
    rcases mem_append.1 hx' with hx' | hx'
    · exact mem_append_left v
        ((suffix_of_suffix_length_le h₁ (suffix_append u m) (by omega)).subset hx')
    · exact mem_append_right m (h₂.subset hx')

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
