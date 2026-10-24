/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Infixes of a three-part concatenation, and chains of prefixes

An infix of `u ++ m ++ v` lies within `u ++ m`, lies within `m ++ v`, or is `m` extended by a
suffix of `u` and a prefix of `v`. So an infix no longer than `m` cannot contain both an element
that occurs only in `u` and an element that occurs only in `v`: this is the fact about short
windows that pumping arguments use, when `m` is a block of the pumped word that separates two
others.

Two prefixes of one list are comparable in the prefix order, so the prefixes `inits` lists ascend
in it, the suffixes `tails` lists descend in the suffix order, and `l.takeWhile q` is a prefix of
`l.takeWhile p` once `q` fails inside `l.takeWhile p`.

## Main results

* `List.infix_append_append_iff`: the infixes of `u ++ m ++ v`, the three-part form of
  `List.infix_append_iff`.
* `List.IsInfix.notMem_or_notMem_of_length_le`: an infix of `u ++ m ++ v` no longer than `m` misses
  every element occurring only in `u` or every element occurring only in `v`.
* `List.pairwise_inits`, `List.pairwise_tails`: `inits` ascends in the prefix order, `tails`
  descends in the suffix order.
* `List.takeWhile_prefix_takeWhile_of_mem`: `l.takeWhile q <+: l.takeWhile p` when some element
  of `l.takeWhile p` fails `q`.

## Implementation notes

[UPSTREAM] candidates: `List.infix_append_append_iff` beside `List.infix_append_iff` in core
`Init/Data/List/Sublist.lean`, the `takeWhile` lemma beside `List.takeWhile_prefix` there, and
the rest for `Mathlib/Data/List/Infix.lean`. The short-window lemma would go up with a pumping
lemma for context-free languages, which mathlib lacks.
-/

@[expose] public section

namespace List

variable {α : Type*} {l l₁ l₂ u m v : List α} {x y : α}

theorem infix_append_append_iff : l <:+: u ++ m ++ v ↔
    l <:+: u ++ m ∨ l <:+: m ++ v ∨ ∃ s t, l = s ++ m ++ t ∧ s <:+ u ∧ t <+: v := by
  refine ⟨fun ⟨s, t, h⟩ ↦ ?_, ?_⟩
  · rw [append_assoc s, append_assoc u] at h
    obtain ⟨a', rfl, h₁⟩ | ⟨c', rfl, h₁⟩ := append_eq_append_iff.1 h
    · rw [← append_assoc] at h₁
      obtain ⟨c, h₂, rfl⟩ | ⟨c, rfl, rfl⟩ := append_eq_append_iff.1 h₁
      · exact .inl ⟨s, c, by rw [append_assoc s, ← h₂, append_assoc]⟩
      · exact .inr (.inr ⟨a', c, rfl, suffix_append s a', prefix_append c t⟩)
    · exact .inr (.inl ⟨c', t, by rw [append_assoc, h₁]⟩)
  · rintro (h | h | ⟨s, t, rfl, ⟨u', rfl⟩, ⟨v', rfl⟩⟩)
    · exact h.trans (prefix_append _ _).isInfix
    · simpa only [append_assoc] using h.trans (suffix_append u (m ++ v)).isInfix
    · exact ⟨u', v', by simp⟩

/-- An infix of `u ++ m ++ v` no longer than `m` misses an element that occurs only in `u` or an
element that occurs only in `v`. -/
theorem IsInfix.notMem_or_notMem_of_length_le (hl : l <:+: u ++ m ++ v)
    (hlen : l.length ≤ m.length) (hx : x ∉ m ++ v) (hy : y ∉ u ++ m) : x ∉ l ∨ y ∉ l := by
  rcases infix_append_append_iff.1 hl with h | h | ⟨s, t, rfl, -, -⟩
  · exact .inr fun hy' ↦ hy (h.subset hy')
  · exact .inl fun hx' ↦ hx (h.subset hx')
  · have hml : m = s ++ m ++ t := (infix_append s m t).eq_of_length_le hlen
    exact .inl fun hx' ↦ hx (mem_append_left v (hml ▸ hx'))

/-- Lists with the same prefixes are equal. -/
theorem eq_of_forall_prefix_iff (h : ∀ r, r <+: l₁ ↔ r <+: l₂) : l₁ = l₂ :=
  antisymm ((h l₁).1 prefix_rfl) ((h l₂).2 prefix_rfl)

/-- The prefixes of a list, as `inits` lists them, ascend in the prefix order. -/
theorem pairwise_inits : ∀ l : List α, l.inits.Pairwise (· <+: ·)
  | [] => by simp
  | a :: l => by
    rw [inits_cons, pairwise_cons, pairwise_map]
    exact ⟨fun _ _ ↦ nil_prefix, (pairwise_inits l).imp fun h ↦ cons_prefix_cons.2 ⟨rfl, h⟩⟩

/-- The suffixes of a list, as `tails` lists them, descend in the suffix order. -/
theorem pairwise_tails : ∀ l : List α, l.tails.Pairwise fun s t ↦ t <:+ s
  | [] => by simp
  | a :: l => pairwise_cons.2
    ⟨fun _ h ↦ ((mem_tails _ _).1 h).trans (suffix_cons a l), pairwise_tails l⟩

/-- What precedes the first failure of `q` is a prefix of what precedes the first failure of `p`,
when some element before the latter fails `q`. -/
theorem takeWhile_prefix_takeWhile_of_mem {p q : α → Bool} (hx : x ∈ l.takeWhile p) (hq : ¬q x) :
    l.takeWhile q <+: l.takeWhile p :=
  (prefix_or_prefix_of_prefix (takeWhile_prefix q) (takeWhile_prefix p)).resolve_right
    fun h ↦ hq (all_eq_true.1 all_takeWhile x (h.subset hx))

end List
