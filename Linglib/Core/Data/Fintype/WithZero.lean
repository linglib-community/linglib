/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Data.Fintype.Option

/-!
# Fintype instances for `WithOne α` and `WithZero α`

`[UPSTREAM]` candidate, the counterpart of `Mathlib/Data/Fintype/WithTopBot.lean` for the types
that adjoin a one or a zero.
-/

public section

variable {α : Type*}

@[to_additive]
instance [Fintype α] : Fintype (WithOne α) :=
  inferInstanceAs <| Fintype (Option α)

@[to_additive]
instance [Finite α] : Finite (WithOne α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _
