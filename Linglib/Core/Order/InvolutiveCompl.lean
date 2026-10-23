/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Involutive complements

This file defines involutive complements. An involutive complement on an ordered type is a
complement `ᶜ` that is involutive, `aᶜᶜ = a`, and reverses the order. It is Birkhoff's
"involution", and a lattice with one is Kalman's "lattice with involution". The De Morgan laws
follow from these two properties alone, without any complementation law such as `a ⊓ aᶜ = ⊥`.

The involution is the common base of two branches between mathlib's lattices and
`BooleanAlgebra`. Adding distributivity gives De Morgan and Kleene algebras
(`Core/Order/DeMorganAlgebra/`); adding non-contradiction gives ortholattices
(`Core/Order/Ortholattice.lean`). A Boolean algebra lies on both.

## Main definitions

* `InvolutiveCompl`: the data class of an involutive, order-reversing complement, extending the
  notation class `Compl` and parameterized by the order, as mathlib's `InvolutiveNeg` extends
  `Neg` and `OrderTop` takes `[LE α]`.
* `InvolutiveCompl.complOrderIso`: the involution as an order isomorphism `α ≃o αᵒᵈ`.

## Main results

* `InvolutiveCompl.compl_sup`, `InvolutiveCompl.compl_inf`: the De Morgan laws.
* `InvolutiveCompl.le_compl_comm`: `a ≤ bᶜ ↔ b ≤ aᶜ`.
* `BooleanAlgebra.toInvolutiveCompl`: a Boolean algebra's complement is involutive.

## Implementation notes

The lemmas are protected in the `InvolutiveCompl` namespace because the root names
(`compl_compl`, `compl_sup`, ...) belong to mathlib's Boolean and Heyting API. Upstream, the
Boolean ones would be generalized to `InvolutiveCompl`, and `complOrderIso` would generalize
mathlib's `OrderIso.compl`. There is no `OrderDual` instance: its complement would have to agree
with the one mathlib's `OrderDual.instBiheytingAlgebra` gives the dual of a Boolean algebra, the
one place a genuine `Compl` diamond can arise.

## References

* [kalman-1958]
-/

@[expose] public section

open OrderDual

variable {α β : Type*}

/-- An **involutive complement** on an ordered type is a complement with `aᶜᶜ = a` that reverses
the order ([kalman-1958]'s involution, Birkhoff's dual automorphism of period two). `Compl` is
notation, so no complementation law is implied: `a ⊓ aᶜ = ⊥` may fail. -/
class InvolutiveCompl (α : Type*) [LE α] extends Compl α where
  /-- The complement is involutive, `aᶜᶜ = a`. -/
  protected compl_compl (a : α) : aᶜᶜ = a
  /-- The complement reverses the order. -/
  protected compl_le_compl {a b : α} : a ≤ b → bᶜ ≤ aᶜ

namespace InvolutiveCompl

section LE

variable [LE α] [InvolutiveCompl α] {a b : α}

protected theorem compl_involutive : Function.Involutive (compl : α → α) :=
  InvolutiveCompl.compl_compl

protected theorem compl_injective : Function.Injective (compl : α → α) :=
  InvolutiveCompl.compl_involutive.injective

protected theorem compl_surjective : Function.Surjective (compl : α → α) :=
  InvolutiveCompl.compl_involutive.surjective

@[simp] protected theorem compl_inj_iff : aᶜ = bᶜ ↔ a = b :=
  InvolutiveCompl.compl_injective.eq_iff

protected theorem compl_eq_iff_eq_compl : aᶜ = b ↔ a = bᶜ :=
  InvolutiveCompl.compl_involutive.eq_iff

@[simp] protected theorem compl_le_compl_iff_le : aᶜ ≤ bᶜ ↔ b ≤ a :=
  ⟨fun h ↦ InvolutiveCompl.compl_compl b ▸ InvolutiveCompl.compl_compl a ▸
    InvolutiveCompl.compl_le_compl h, InvolutiveCompl.compl_le_compl⟩

/-- Orthogonality is symmetric, `a ≤ bᶜ ↔ b ≤ aᶜ`. -/
protected theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ :=
  ⟨fun h ↦ InvolutiveCompl.compl_compl b ▸ InvolutiveCompl.compl_le_compl h,
    fun h ↦ InvolutiveCompl.compl_compl a ▸ InvolutiveCompl.compl_le_compl h⟩

variable (α) in
/-- The involution bundled as an order isomorphism onto the order dual. Upstream this is mathlib's
`OrderIso.compl`, generalized from `BooleanAlgebra` to `InvolutiveCompl`. -/
def complOrderIso : α ≃o αᵒᵈ where
  toFun a := toDual aᶜ
  invFun a := (ofDual a)ᶜ
  left_inv := InvolutiveCompl.compl_compl
  right_inv a := congrArg toDual (InvolutiveCompl.compl_compl (ofDual a))
  map_rel_iff' := InvolutiveCompl.compl_le_compl_iff_le

end LE

protected theorem compl_anti [Preorder α] [InvolutiveCompl α] : Antitone (compl : α → α) :=
  fun _ _ h ↦ InvolutiveCompl.compl_le_compl h

/-! The De Morgan laws and the exchange of the bounds are `complOrderIso` preserving the lattice
operations: they follow from involution and antitonicity alone. -/

section Lattice

variable [Lattice α] [InvolutiveCompl α]

@[simp] protected theorem compl_sup (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  (complOrderIso α).map_sup a b

@[simp] protected theorem compl_inf (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ :=
  (complOrderIso α).map_inf a b

end Lattice

section BoundedOrder

variable [PartialOrder α] [BoundedOrder α] [InvolutiveCompl α]

@[simp] protected theorem compl_bot : (⊥ : α)ᶜ = ⊤ := (complOrderIso α).map_bot

@[simp] protected theorem compl_top : (⊤ : α)ᶜ = ⊥ := (complOrderIso α).map_top

end BoundedOrder

end InvolutiveCompl

/-- A Boolean algebra's complement is involutive and antitone. -/
instance (priority := 100) BooleanAlgebra.toInvolutiveCompl [BooleanAlgebra α] :
    InvolutiveCompl α where
  compl_compl := compl_compl
  compl_le_compl h := compl_le_compl h

/-! ### Products and functions -/

instance [LE α] [LE β] [InvolutiveCompl α] [InvolutiveCompl β] : InvolutiveCompl (α × β) where
  compl_compl p := Prod.ext (InvolutiveCompl.compl_compl p.1) (InvolutiveCompl.compl_compl p.2)
  compl_le_compl h := ⟨InvolutiveCompl.compl_le_compl h.1, InvolutiveCompl.compl_le_compl h.2⟩

instance {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] [∀ i, InvolutiveCompl (π i)] :
    InvolutiveCompl (∀ i, π i) where
  compl_compl f := funext fun i ↦ InvolutiveCompl.compl_compl (f i)
  compl_le_compl h i := InvolutiveCompl.compl_le_compl (h i)
