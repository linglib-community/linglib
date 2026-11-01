/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.FreeSemigroup`, next to
`FreeSemigroup.toFreeMonoid_ne_one`.
-/
module

public import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# Nonempty words

The words of the free semigroup, read in the free monoid, are nonempty.
-/

@[expose] public section

variable {α : Type*} (u : FreeSemigroup α)

@[simp] theorem FreeSemigroup.toList_toFreeMonoid_ne_nil :
    u.toFreeMonoid.toList ≠ [] := fun h ↦
  toFreeMonoid_ne_one u (FreeMonoid.toList.injective h)
