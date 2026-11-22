/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Atoms

/-!
# Atoms and simple orders

`[UPSTREAM]` An upper bound of a nonempty set of atoms is an atom exactly when the set is its
singleton, and likewise for minimal elements of an order with no least element: the least upper
bound of two or more atoms is not one. In a simple order the only strict pair is `⊥ < ⊤`:
mathlib proves each half
(`IsSimpleOrder.eq_bot_of_lt`, `IsSimpleOrder.eq_top_of_lt`) and the special case `Bool.lt_iff`,
and the characterization holds for every simple order, so a two-element scale inherits it from its
`IsSimpleOrder` instance.
-/

public section

section UpperBounds

variable {α : Type*} [PartialOrder α] {s : Set α} {a : α}

/-- An upper bound of a nonempty set of minimal elements is minimal exactly when the set is its
singleton. -/
theorem isMin_iff_eq_singleton_of_mem_upperBounds (ha : a ∈ upperBounds s) (hne : s.Nonempty)
    (hs : ∀ x ∈ s, IsMin x) : IsMin a ↔ s = {a} :=
  ⟨fun h ↦ hne.subset_singleton_iff.1 fun _ hx ↦ le_antisymm (ha hx) (h (ha hx)),
    fun h ↦ hs a (h.symm ▸ Set.mem_singleton a)⟩

/-- An upper bound of a nonempty set of atoms is an atom exactly when the set is its
singleton. -/
theorem isAtom_iff_eq_singleton_of_mem_upperBounds [OrderBot α] (ha : a ∈ upperBounds s)
    (hne : s.Nonempty) (hs : ∀ x ∈ s, IsAtom x) : IsAtom a ↔ s = {a} :=
  ⟨fun h ↦ hne.subset_singleton_iff.1 fun x hx ↦
      (h.le_iff.1 (ha hx)).resolve_left (hs x hx).1,
    fun h ↦ hs a (h.symm ▸ Set.mem_singleton a)⟩

end UpperBounds

namespace IsSimpleOrder

variable {α : Type*} [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α}

theorem lt_iff_eq_bot_and_eq_top : a < b ↔ a = ⊥ ∧ b = ⊤ :=
  ⟨fun h ↦ ⟨eq_bot_of_lt h, eq_top_of_lt h⟩, fun ⟨ha, hb⟩ ↦ ha ▸ hb ▸ bot_lt_top⟩

end IsSimpleOrder
