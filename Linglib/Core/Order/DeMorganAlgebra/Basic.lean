/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.InvolutiveCompl

/-!
# De Morgan and Kleene algebras

In classical logic the conjunction of a sentence with its negation has the least value, and their
disjunction the greatest. Kleene's three-valued negation gives up both laws and keeps two others: it
reverses the order of truth, and it cancels when doubled. A **De Morgan algebra** is a bounded
distributive lattice with such a negation, an involutive complement. A **Kleene algebra** adds
Kleene's law, that a contradiction *a* ⊓ *a*ᶜ lies below every excluded middle *b* ⊔ *b*ᶜ. Kalman's
"normal" lattices with involution are the distributive lattices satisfying it, with or without
bounds. Every Boolean algebra is a Kleene algebra, since there a contradiction is the least element,
and Kleene's three truth values are the standard example that is not Boolean.

## Main definitions

* `IsKleene`: the Kleene law, a Prop mixin over `[Lattice α] [InvolutiveCompl α]`.

## Main results

* `BooleanAlgebra.toIsKleene`: every Boolean algebra is a Kleene algebra.
* `Prod` and `Pi` instances of `IsKleene`.

## Implementation notes

A De Morgan algebra is written `[DistribLattice α] [BoundedOrder α] [InvolutiveCompl α]` and needs
no class of its own. "Kleene algebra" here is the lattice notion, not the regular-expression
star-semiring of mathlib's root `KleeneAlgebra`. Kalman's construction of Kleene algebras from
distributive lattices is in `Core/Order/DeMorganAlgebra/Kalman.lean`.

## References

* [kalman-1958]
-/

@[expose] public section

variable {α β : Type*}

/-- A lattice with an involutive complement satisfies **Kleene's law** when the meet of any element
with its complement lies below the join of any element with its complement, so that contradictions
lie below excluded middles. Kalman's "normal" i-lattices are the distributive lattices with an
involution satisfying it, and with bounds they are the Kleene algebras. -/
class IsKleene (α : Type*) [Lattice α] [InvolutiveCompl α] : Prop where
  /-- The Kleene law. -/
  inf_compl_le_sup_compl (a b : α) : a ⊓ aᶜ ≤ b ⊔ bᶜ

/-- Every Boolean algebra satisfies Kleene's law, since there the meet of an element with its
complement is the least element. -/
instance (priority := 100) BooleanAlgebra.toIsKleene [BooleanAlgebra α] : IsKleene α :=
  ⟨fun a _ ↦ (BooleanAlgebra.inf_compl_le_bot a).trans _root_.bot_le⟩

instance [Lattice α] [Lattice β] [InvolutiveCompl α] [InvolutiveCompl β] [IsKleene α]
    [IsKleene β] : IsKleene (α × β) :=
  ⟨fun a b ↦ ⟨IsKleene.inf_compl_le_sup_compl a.1 b.1, IsKleene.inf_compl_le_sup_compl a.2 b.2⟩⟩

instance {ι : Type*} {π : ι → Type*} [∀ i, Lattice (π i)] [∀ i, InvolutiveCompl (π i)]
    [∀ i, IsKleene (π i)] : IsKleene (∀ i, π i) :=
  ⟨fun f g i ↦ IsKleene.inf_compl_le_sup_compl (f i) (g i)⟩
