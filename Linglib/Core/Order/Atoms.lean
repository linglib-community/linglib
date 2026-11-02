/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Atoms

/-!
# Simple orders

`[UPSTREAM]` In a simple order the only strict pair is `⊥ < ⊤`: mathlib proves each half
(`IsSimpleOrder.eq_bot_of_lt`, `IsSimpleOrder.eq_top_of_lt`) and the special case `Bool.lt_iff`,
and the characterization holds for every simple order, so a two-element scale inherits it from its
`IsSimpleOrder` instance.
-/

public section

namespace IsSimpleOrder

variable {α : Type*} [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α}

theorem lt_iff_eq_bot_and_eq_top : a < b ↔ a = ⊥ ∧ b = ⊤ :=
  ⟨fun h ↦ ⟨eq_bot_of_lt h, eq_top_of_lt h⟩, fun ⟨ha, hb⟩ ↦ ha ▸ hb ▸ bot_lt_top⟩

end IsSimpleOrder
