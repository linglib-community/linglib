/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Zip

/-!
# `revzip` of a mapped list

`List.revzip_map`: `revzip` commutes with `map`, componentwise, the `map` companion of
`List.revzip_map_fst` and `List.revzip_map_snd` and the `revzip` instance of `List.zip_map`.
[UPSTREAM] candidate for `Mathlib/Data/List/Zip.lean`.
-/

public section

namespace List

variable {α β : Type*}

@[simp] theorem revzip_map (f : α → β) (l : List α) :
    (l.map f).revzip = l.revzip.map (Prod.map f f) := by
  rw [revzip, revzip, ← map_reverse, zip_map]

end List
