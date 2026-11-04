/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Order.SupClosed

/-!
# Distributive join-semilattices

[UPSTREAM] candidate for a new `Mathlib/Order/DistribSemilattice.lean`.

A join-semilattice is *distributive* when every element below a join `b ⊔ c` is the join of an
element below `b` and an element below `c`. Every distributive lattice is distributive in this
sense, and a lattice that is distributive in this sense obeys the distributive law
([`inf_sup_le`](##IsDistribSemilatticeSup.inf_sup_le)), so the notion extends distributivity to
semilattices that lack meets. Any two elements of a distributive semilattice have a lower bound,
and the largest lower set inside a sup-closed set is again sup-closed.

## Main definitions

* `IsDistribSemilatticeSup α`: `α` is a distributive join-semilattice.
-/

@[expose] public section

variable {α : Type*}

/-- A join-semilattice is distributive when every element below `b ⊔ c` is the join of an element
below `b` and an element below `c`. -/
class IsDistribSemilatticeSup (α : Type*) [SemilatticeSup α] : Prop where
  /-- An element below a join splits along the join. -/
  exists_sup_eq_of_le_sup {a b c : α} (h : a ≤ b ⊔ c) : ∃ b' ≤ b, ∃ c' ≤ c, b' ⊔ c' = a

export IsDistribSemilatticeSup (exists_sup_eq_of_le_sup)

instance (priority := 100) DistribLattice.toIsDistribSemilatticeSup [DistribLattice α] :
    IsDistribSemilatticeSup α where
  exists_sup_eq_of_le_sup {a b c} h :=
    ⟨a ⊓ b, inf_le_right, a ⊓ c, inf_le_right, by rw [← inf_sup_left, inf_eq_left.2 h]⟩

/-- The distributive law, in a lattice distributive as a semilattice. -/
theorem IsDistribSemilatticeSup.inf_sup_le [Lattice α] [IsDistribSemilatticeSup α] (a b c : α) :
    a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := by
  obtain ⟨b', hb, c', hc, h⟩ := exists_sup_eq_of_le_sup (inf_le_right : a ⊓ (b ⊔ c) ≤ b ⊔ c)
  have ha : b' ⊔ c' ≤ a := h.le.trans inf_le_left
  rw [← h]
  exact sup_le_sup (le_inf (le_sup_left.trans ha) hb) (le_inf (le_sup_right.trans ha) hc)

variable [SemilatticeSup α] [IsDistribSemilatticeSup α]

instance (priority := 50) IsDistribSemilatticeSup.toIsCodirectedOrder : IsCodirectedOrder α where
  directed a b :=
    let ⟨_, _, c, hc, h⟩ := exists_sup_eq_of_le_sup (le_sup_left : a ≤ a ⊔ b)
    ⟨c, h ▸ le_sup_right, hc⟩

/-- The largest lower set inside a sup-closed set is sup-closed. -/
theorem SupClosed.setOf_forall_le {s : Set α} (hs : SupClosed s) :
    SupClosed {x | ∀ y ≤ x, y ∈ s} := fun _ ha _ hb _ hc ↦
  let ⟨a', ha', b', hb', h⟩ := exists_sup_eq_of_le_sup hc
  h ▸ hs (ha a' ha') (hb b' hb')
