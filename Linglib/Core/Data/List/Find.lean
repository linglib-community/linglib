/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Find

/-!
# `List.find?` under a stronger predicate

The first element of a list satisfying `q` is also the first satisfying any predicate `p` that
it satisfies and that implies `q` on the list, since an earlier element satisfying `p` would
satisfy `q`. [UPSTREAM] candidate for `Mathlib/Data/List/Find.lean`.

## Main results

* `List.find?_eq_some_of_imp`: `find?` stays put under a stronger predicate the found element
  satisfies.
-/

public section

namespace List

variable {α : Type*} {p q : α → Bool} {l : List α} {a : α}

/-- The first element satisfying `q` is the first satisfying any stronger predicate it
satisfies. -/
theorem find?_eq_some_of_imp (hq : l.find? q = some a) (hp : p a)
    (h : ∀ x ∈ l, p x → q x) : l.find? p = some a := by
  induction l with grind

end List
