/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Fin

/-!
# Counting the positions of a list

`Fin.card_filter_univ_getElem_eq_countP`: the positions of a list whose element satisfies a
predicate number as many as the elements satisfying it, the `List` counterpart of
`Fin.card_filter_univ_eq_vector_get_eq_count`.
[UPSTREAM] candidate for `Mathlib/Data/Fintype/Fin.lean`.
-/

@[expose] public section

open Finset

namespace Fin

variable {α : Type*}

theorem card_filter_univ_getElem_eq_countP (l : List α) (p : α → Bool) :
    #{i : Fin l.length | p l[i]} = l.countP p := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    refine (card_filter_univ_succ' (n := xs.length) fun i ↦ p (x :: xs)[i] = true).trans ?_
    rw [List.countP_cons, ← ih]
    by_cases h : p x <;> simp [h, add_comm]

end Fin
