/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# The Bregman divergence along a functional

For functions `V g : E → β` into an additive group, we define the Bregman divergence of `V` from
`p` to `q` along `g` as `bregmanDiv V g p q = V q - V p - (g q - g p)`, the gap at `q` between `V`
and the function `V p + (g · - g p)` that agrees with `V` at `p` and varies as `g` does. When `g`
is additive on a group `E` this is `V q - V p - g (q - p)`, the Bregman divergence of a convex
function `V` whose subgradient at `p` is `g`. The divergence is nonnegative exactly when that
function lies below `V` at `q` (`bregmanDiv_nonneg_iff`), which is what it is for `g` to support
`V` at `p`.

## Implementation notes

The slope is a function on `E` and not a linear functional on differences, so that the
definition applies where `E` has no subtraction, as on measures, where `g` integrates a fixed
function.
-/

@[expose] public section

variable {E β : Type*} [AddCommGroup β]

/-- The Bregman divergence of `V` from `p` to `q` along `g` is the gap at `q` between `V` and the
function that agrees with `V` at `p` and varies as `g`. -/
def bregmanDiv (V g : E → β) (p q : E) : β := V q - V p - (g q - g p)

variable {V g : E → β} {p q : E}

@[simp] theorem bregmanDiv_self : bregmanDiv V g p p = 0 := by simp [bregmanDiv]

theorem bregmanDiv_eq_sub_map_sub {E F : Type*} [AddGroup E] [FunLike F E β]
    [AddMonoidHomClass F E β] (V : E → β) (g : F) (p q : E) :
    bregmanDiv V g p q = V q - V p - g (q - p) := by
  rw [bregmanDiv, map_sub]

theorem bregmanDiv_nonneg_iff [PartialOrder β] [IsOrderedAddMonoid β] :
    0 ≤ bregmanDiv V g p q ↔ V p + (g q - g p) ≤ V q := by
  rw [bregmanDiv, sub_nonneg, le_sub_iff_add_le']
