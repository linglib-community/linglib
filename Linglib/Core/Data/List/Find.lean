/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Find
public import Mathlib.Order.Bounds.Defs

/-!
# Finding in a list

The first element of a list satisfying `q` is also the first satisfying any predicate `p` that
it satisfies and that implies `q` on the list, since an earlier element satisfying `p` would
satisfy `q`, and `List.idxOf` gives the least index of a value in a list. [UPSTREAM] candidates for
`Mathlib/Data/List/Find.lean`.

## Main results

* `List.find?_eq_some_of_imp`: `find?` stays put under a stronger predicate the found element
  satisfies.
* `List.isLeast_idxOf`: `idxOf` is the least index of a value in the list.
-/

public section

namespace List

variable {α : Type*} {p q : α → Bool} {l : List α} {a : α}

/-- The first element satisfying `q` is the first satisfying any stronger predicate it
satisfies. -/
theorem find?_eq_some_of_imp (hq : l.find? q = some a) (hp : p a)
    (h : ∀ x ∈ l, p x → q x) : l.find? p = some a := by
  induction l with grind

/-- `idxOf` is the least index of a value in the list. -/
theorem isLeast_idxOf [BEq α] [LawfulBEq α] (h : a ∈ l) :
    IsLeast {i | l[i]? = some a} (l.idxOf a) := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · change l[l.idxOf a]? = some a
    rw [getElem?_eq_getElem (idxOf_lt_length_iff.2 h), getElem_idxOf]
  · clear h
    induction l generalizing j with
    | nil => simp at hj
    | cons b l ih =>
      by_cases hb : b = a
      · simp [hb]
      · cases j with
        | zero => simp [hb] at hj
        | succ j => simpa [idxOf_cons, hb] using ih (j := j) (by simpa using hj)

end List
