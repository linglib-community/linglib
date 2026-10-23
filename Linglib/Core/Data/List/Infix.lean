/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Infixes of a three-part concatenation, and prefixes

An infix of `u ++ m ++ v` lies within `u ++ m`, lies within `m ++ v`, or contains `m`. So an infix
no longer than `m` cannot contain both an element that occurs only in `u` and an element that
occurs only in `v`: this is the fact about short windows that pumping arguments use, when `m` is a
block of the pumped word that separates two others.

The longest common prefix `List.commonPrefix l₁ l₂` is the greatest list that is a prefix of
both, the meet of the prefix order.

## Main definitions

* `List.commonPrefix`: the longest common prefix of two lists.

## Main results

* `List.IsInfix.infix_append_or_infix_append_or_infix`: an infix of `u ++ m ++ v` is an infix of
  `u ++ m` or of `m ++ v`, or contains `m`.
* `List.IsInfix.notMem_or_notMem_of_length_le`: an infix of `u ++ m ++ v` no longer than `m` misses
  every element occurring only in `u` or every element occurring only in `v`.
* `List.pairwise_inits`: the prefixes `inits` lists ascend in the prefix order.
* `List.takeWhile_bne_prefix_of_mem`: what precedes the first `c` is a prefix of what precedes
  the first `d`, when `c` comes before the first `d`.

## Implementation notes

[UPSTREAM] candidate: `Mathlib/Data/List/Infix.lean`, or core `Init/Data/List/Sublist.lean` beside
`List.infix_append_iff`. Neither core, Batteries nor mathlib defines a longest common prefix of
lists.
-/

@[expose] public section

namespace List

variable {α : Type*} {l u m v : List α} {x y : α}

/-- An infix of `u ++ m ++ v` is an infix of `u ++ m`, an infix of `m ++ v`, or contains `m`. -/
theorem IsInfix.infix_append_or_infix_append_or_infix (hl : l <:+: u ++ m ++ v) :
    l <:+: u ++ m ∨ l <:+: m ++ v ∨ m <:+: l := by
  obtain ⟨s, t, h⟩ := hl
  rw [append_assoc s, append_assoc u] at h
  obtain ⟨a', rfl, h₁⟩ | ⟨c', rfl, h₁⟩ := append_eq_append_iff.1 h
  · rw [← append_assoc] at h₁
    obtain ⟨c, h₂, rfl⟩ | ⟨c, rfl, rfl⟩ := append_eq_append_iff.1 h₁
    · exact .inl ⟨s, c, by rw [append_assoc s, ← h₂, append_assoc]⟩
    · exact .inr (.inr ⟨a', c, rfl⟩)
  · exact .inr (.inl ⟨c', t, by rw [append_assoc, h₁]⟩)

/-- An infix of `u ++ m ++ v` no longer than `m` misses an element that occurs only in `u` or an
element that occurs only in `v`. -/
theorem IsInfix.notMem_or_notMem_of_length_le (hl : l <:+: u ++ m ++ v)
    (hlen : l.length ≤ m.length) (hx : x ∉ m ++ v) (hy : y ∉ u ++ m) : x ∉ l ∨ y ∉ l := by
  rcases hl.infix_append_or_infix_append_or_infix with h | h | h
  · exact .inr fun hy' ↦ hy (h.subset hy')
  · exact .inl fun hx' ↦ hx (h.subset hx')
  · exact .inl fun hx' ↦ hx (mem_append_left v (h.eq_of_length_le hlen ▸ hx'))

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

/-- An element before the first `d` cuts off a prefix of what comes before the first `d`. -/
theorem takeWhile_bne_prefix_of_mem {c d : α} :
    ∀ {l : List α}, c ∈ l.takeWhile (· != d) → l.takeWhile (· != c) <+: l.takeWhile (· != d)
  | [], _ => by simp
  | x :: l, h => by
    by_cases hxd : x = d
    · simp [hxd] at h
    by_cases hxc : x = c
    · simp [hxc]
    have hd : (x :: l).takeWhile (· != d) = x :: l.takeWhile (· != d) := by simp [hxd]
    have hc : (x :: l).takeWhile (· != c) = x :: l.takeWhile (· != c) := by simp [hxc]
    rw [hd] at h
    rw [hd, hc]
    exact cons_prefix_cons.2 ⟨rfl,
      takeWhile_bne_prefix_of_mem ((mem_cons.1 h).resolve_left (Ne.symm hxc))⟩

end DecidableEq

/-- The prefixes of a list, as `inits` lists them, ascend in the prefix order. -/
theorem pairwise_inits : ∀ l : List α, l.inits.Pairwise (· <+: ·)
  | [] => by simp
  | a :: l => by
    rw [inits_cons, pairwise_cons, pairwise_map]
    exact ⟨fun _ _ ↦ nil_prefix, (pairwise_inits l).imp fun h ↦ cons_prefix_cons.2 ⟨rfl, h⟩⟩

end List
