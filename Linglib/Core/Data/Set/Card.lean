/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Card

/-!
# Cardinalities of predicate extensions

Mirror of `Mathlib/Data/Set/Card.lean`: on a finite type the `Set.ncard` of a predicate's
extension is the cardinality of its `Finset` filter, at any decidability instance, so a
statement about `Set.ncard` evaluates by `decide`. [UPSTREAM]
-/

@[expose] public section

namespace Set

variable {α : Type*}

theorem ncard_setOf_eq_card_filter [Fintype α] (p : α → Prop) [DecidablePred p] :
    {x | p x}.ncard = (Finset.univ.filter p).card := by
  rw [ncard_eq_toFinset_card', toFinset_ofPred]

end Set
