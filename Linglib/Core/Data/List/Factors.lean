/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix
public import Linglib.Core.Data.List.DropRight

/-!
# Length-`k` infixes of a list

`List.kFactors k xs` lists the contiguous length-`k` infixes of `xs`, the infix sibling of
`List.sublistsLen` (length-`k` subsequences): `List.mem_kFactors` characterizes membership as
`f <:+: xs ∧ f.length = k`, and `List.kFactors_cons` is the recursion that computes it. The
name is the subregular literature's "`k`-factor"; mathlib has no length-`k` infix enumerator.

## Main definitions

* `List.kFactors`: the contiguous length-`k` infixes of a list, in order of occurrence.

## Main results

* `List.mem_kFactors`: membership is being a length-`k` infix, mirroring `List.mem_sublistsLen`.
* `List.kFactors_nil`, `List.kFactors_cons`, `List.kFactors_two_cons_cons`: the recursion, and its
  `k = 2` form used by chain characterizations of the strictly 2-local languages.
* `List.mem_kFactors_append`: a `k`-factor of a concatenation lies in one of the two words or
  across the seam between them.
* `List.kFactors_map`: mapping a function over a list maps it over the `k`-factors.
-/

@[expose] public section

namespace List

variable {α : Type*} {k : ℕ} {xs f : List α}

/-- The contiguous length-`k` infixes of `xs`, in order of occurrence: the length-`k` prefixes
of the suffixes long enough to have one. -/
def kFactors (k : ℕ) (xs : List α) : List (List α) :=
  (xs.tails.filter (k ≤ ·.length)).map (·.take k)

theorem mem_kFactors : f ∈ kFactors k xs ↔ f <:+: xs ∧ f.length = k := by
  simp only [kFactors, mem_map, mem_filter, mem_tails, decide_eq_true_eq]
  constructor
  · rintro ⟨s, ⟨hs, hk⟩, rfl⟩
    exact ⟨(take_prefix _ s).isInfix.trans hs.isInfix, length_take_of_le hk⟩
  · rintro ⟨⟨s, t, rfl⟩, rfl⟩
    exact ⟨f ++ t, ⟨⟨s, by simp⟩, by simp⟩, by simp⟩

@[simp] theorem kFactors_nil : kFactors k ([] : List α) = if k = 0 then [[]] else [] := by
  rcases k with _ | k <;> simp [kFactors]

@[simp] theorem kFactors_cons (a : α) (l : List α) :
    kFactors k (a :: l) =
      if k ≤ l.length + 1 then (a :: l).take k :: kFactors k l else kFactors k l := by
  simp only [kFactors, tails_cons, filter_cons, length_cons, decide_eq_true_eq]
  split_ifs <;> simp

theorem kFactors_two_cons_cons (a b : α) (rest : List α) :
    kFactors 2 (a :: b :: rest) = [a, b] :: kFactors 2 (b :: rest) := by
  rw [kFactors_cons, ite_eq_left (by simp)]; rfl

theorem mem_kFactors_append {u v : List α} :
    f ∈ kFactors k (u ++ v) ↔ f ∈ kFactors k u ∨ f ∈ kFactors k v ∨
      f ∈ kFactors k (u.rtake (k - 1) ++ v.take (k - 1)) := by
  simp only [mem_kFactors]
  constructor
  · rintro ⟨hf, rfl⟩
    rcases infix_append_iff_ne_nil.mp hf with h | h | ⟨l₁, l₂, h₁, h₂, rfl, hu, hv⟩
    · exact .inl ⟨h, rfl⟩
    · exact .inr (.inl ⟨h, rfl⟩)
    · have := length_pos_iff.mpr h₁
      have := length_pos_iff.mpr h₂
      refine .inr (.inr ⟨infix_append_iff.mpr (.inr (.inr ⟨l₁, l₂, rfl, ?_, ?_⟩)), rfl⟩)
      · refine suffix_of_suffix_length_le hu (rtake_suffix _ _) ?_
        have := hu.length_le
        simp only [length_rtake, length_append]; omega
      · refine prefix_of_prefix_length_le hv (take_prefix _ _) ?_
        have := hv.length_le
        simp only [length_take, length_append]; omega
  · rintro (⟨h, hk⟩ | ⟨h, hk⟩ | ⟨h, hk⟩)
    · exact ⟨h.trans (prefix_append u v).isInfix, hk⟩
    · exact ⟨h.trans (suffix_append u v).isInfix, hk⟩
    · exact ⟨h.trans (infix_append_iff.mpr
        (.inr (.inr ⟨_, _, rfl, rtake_suffix _ _, take_prefix _ _⟩))), hk⟩

@[simp] theorem kFactors_map {β : Type*} (g : α → β) (xs : List α) :
    kFactors k (xs.map g) = (kFactors k xs).map (map g) := by
  induction xs with
  | nil => simp only [map_nil, kFactors_nil]; split_ifs <;> rfl
  | cons a l ih =>
    rw [map_cons, kFactors_cons, kFactors_cons, ih, length_map]
    split_ifs <;> simp [map_take]

end List
