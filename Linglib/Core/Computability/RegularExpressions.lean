/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.RegularExpressions

/-!
# The regular expression of the sublists of a word

The sublists of a word `w` form a regular language, matched by the product of the letters of
`w`, each made optional. It is the dual of the shuffle ideal of `w`
(`Language.shuffleIdeal`), the words of which `w` is a sublist.

## Main definitions

* `RegularExpression.sublists w`: the letters of `w` in order, each optional.

## Main results

* `RegularExpression.matches'_sublists`: `sublists w` matches exactly the sublists of `w`.
-/

@[expose] public section

open List

namespace RegularExpression

variable {α : Type*}

/-- The regular expression of the sublists of `w`: its letters in order, each optional. -/
def sublists (w : List α) : RegularExpression α := w.foldr (fun a P ↦ (char a + 1) * P) 1

@[simp] theorem sublists_nil : sublists ([] : List α) = 1 := rfl

@[simp] theorem sublists_cons (a : α) (w : List α) :
    sublists (a :: w) = (char a + 1) * sublists w := rfl

/-- `sublists w` matches exactly the sublists of `w`. -/
theorem matches'_sublists (w : List α) : (sublists w).matches' = {v | v <+ w} := by
  induction w with
  | nil =>
    ext v
    rw [sublists_nil, matches'_epsilon, Language.mem_one]
    exact List.sublist_nil.symm
  | cons a w ih =>
    ext v
    simp only [sublists_cons, matches'_mul, matches'_add, matches'_char, matches'_epsilon, ih,
      Language.mem_mul, Language.mem_add, Language.mem_one, List.sublist_cons_iff]
    constructor
    · rintro ⟨x, hx | rfl, y, hy, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact .inr ⟨y, by simp [hx], hy⟩
      · exact .inl hy
    · rintro (h | ⟨r, rfl, h⟩)
      · exact ⟨[], .inr rfl, v, h, rfl⟩
      · exact ⟨[a], .inl rfl, r, h, rfl⟩

theorem mem_matches'_sublists {v w : List α} : v ∈ (sublists w).matches' ↔ v <+ w := by
  rw [matches'_sublists]; rfl

end RegularExpression
