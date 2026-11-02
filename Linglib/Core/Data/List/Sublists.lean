/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Sublists

/-!
# Sublists paired with their complements

`l.sublists'.revzip` pairs each sublist of `l` with the complementary sublist
(`List.revzip_sublists'`). This file gives its head recursion, the `revzip` companion of
`List.sublists'_cons`: a sublist of `a :: l` either omits `a`, so `a` joins the complement, or
starts with `a`. [UPSTREAM] candidate for `Mathlib/Data/List/Sublists.lean`.

## Main results

* `List.revzip_sublists'_cons`: the head recursion of `sublists'.revzip`.
* `List.revzip_singleton`: the base case.
-/

public section

namespace List

variable {α : Type*}

@[simp] theorem revzip_singleton (a : α) : [a].revzip = [(a, a)] := rfl

theorem revzip_sublists'_cons (a : α) (l : List α) :
    (a :: l).sublists'.revzip =
      l.sublists'.revzip.map (Prod.map id (a :: ·)) ++
        l.sublists'.revzip.map (Prod.map (a :: ·) id) := by
  rw [sublists'_cons, revzip, reverse_append, ← map_reverse, zip_append (by simp), zip_map_right,
    zip_map_left]
  rfl

end List
