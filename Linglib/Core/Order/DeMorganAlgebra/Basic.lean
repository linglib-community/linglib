/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.InvolutiveCompl

/-!
# De Morgan and Kleene algebras

This file defines Kleene's law for lattices with an involutive complement. A *De Morgan algebra*
is a bounded distributive lattice with an involutive complement, written
`[DistribLattice α] [BoundedOrder α] [InvolutiveCompl α]` and needing no class of its own. A
*Kleene algebra* adds Kleene's law `a ⊓ aᶜ ≤ b ⊔ bᶜ`, that contradictions lie below excluded
middles; Kalman's "normal" lattices with involution are the distributive lattices satisfying it,
with or without bounds. Every Boolean algebra is a Kleene algebra, the law degenerating through
`⊥`, and the three-element chain of Kleene's values (`Trivalent`) is the canonical non-Boolean example.

"Kleene algebra" here is the lattice notion, not the regular-expression star-semiring of
mathlib's root `KleeneAlgebra`. Kalman's construction of Kleene algebras from distributive
lattices is in `Core/Order/DeMorganAlgebra/Kalman.lean`.

## Main definitions

* `IsKleene`: the Kleene law, a Prop mixin over `[Lattice α] [InvolutiveCompl α]`.

## Main results

* `BooleanAlgebra.toIsKleene`: every Boolean algebra is a Kleene algebra.
* `Prod` and `Pi` instances of `IsKleene`.

## References

* [kalman-1958]
-/

@[expose] public section

variable {α β : Type*}

/-- Kleene's law says that contradictions lie below excluded middles. [kalman-1958]'s
"normal" i-lattices are the distributive lattices with an involution satisfying it; with bounds
they are the Kleene algebras, the lattice notion. -/
class IsKleene (α : Type*) [Lattice α] [InvolutiveCompl α] : Prop where
  /-- The Kleene law. -/
  inf_compl_le_sup_compl (a b : α) : a ⊓ aᶜ ≤ b ⊔ bᶜ

/-- Every Boolean algebra satisfies the Kleene law, which degenerates through `⊥`. -/
instance (priority := 100) BooleanAlgebra.toIsKleene [BooleanAlgebra α] : IsKleene α :=
  ⟨fun a _ ↦ (BooleanAlgebra.inf_compl_le_bot a).trans _root_.bot_le⟩

instance [Lattice α] [Lattice β] [InvolutiveCompl α] [InvolutiveCompl β] [IsKleene α]
    [IsKleene β] : IsKleene (α × β) :=
  ⟨fun a b ↦ ⟨IsKleene.inf_compl_le_sup_compl a.1 b.1, IsKleene.inf_compl_le_sup_compl a.2 b.2⟩⟩

instance {ι : Type*} {π : ι → Type*} [∀ i, Lattice (π i)] [∀ i, InvolutiveCompl (π i)]
    [∀ i, IsKleene (π i)] : IsKleene (∀ i, π i) :=
  ⟨fun f g i ↦ IsKleene.inf_compl_le_sup_compl (f i) (g i)⟩
