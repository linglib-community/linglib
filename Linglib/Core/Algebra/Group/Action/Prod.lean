/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Action.Prod`.
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Prod

/-!
# Free actions on products

A group acts freely on a product as soon as it acts freely on the first factor, since a group
element fixing a pair fixes each coordinate.
-/

@[expose] public section

namespace Prod

variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

/-- A group acts freely on a product when it acts freely on the first factor. -/
@[to_additive /-- An additive group acts freely on a product when it acts freely on the first
factor. -/]
instance [IsCancelSMul G α] : IsCancelSMul G (α × β) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun _ _ h ↦ IsCancelSMul.eq_one_of_smul congr($h.1)

end Prod
