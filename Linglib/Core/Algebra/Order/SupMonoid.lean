/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Join as multiplication

For a join-semilattice `L` with a bottom and a top, `SupMonoid L` is `L` read as a commutative
monoid with zero: the product is the join, the unit is `⊥` and the zero is `⊤`. It lets a
structure built from a monoid, such as `SetSemiring` or a monoid algebra, be formed over a
semilattice of pieces of information whose join is their combination and whose top is failure.
[UPSTREAM]
-/

@[expose] public section

/-- A bounded join-semilattice read as a commutative monoid with zero. -/
def SupMonoid (L : Type*) := L

namespace SupMonoid

variable {L : Type*}

/-- The identity, into the monoid. -/
def of : L ≃ SupMonoid L := Equiv.refl _

variable [SemilatticeSup L] [OrderBot L] [OrderTop L]

instance : CommMonoidWithZero (SupMonoid L) where
  mul a b := of (of.symm a ⊔ of.symm b)
  one := of ⊥
  zero := of ⊤
  mul_assoc a b c := @sup_assoc L _ a b c
  mul_comm a b := @sup_comm L _ a b
  one_mul a := @bot_sup_eq L _ _ a
  mul_one a := @sup_bot_eq L _ _ a
  zero_mul a := @top_sup_eq L _ _ a
  mul_zero a := @sup_top_eq L _ _ a

theorem of_sup (a b : L) : of (a ⊔ b) = of a * of b := rfl

theorem of_bot : of (⊥ : L) = 1 := rfl

theorem of_top : of (⊤ : L) = 0 := rfl

theorem symm_mul (a b : SupMonoid L) : of.symm (a * b) = of.symm a ⊔ of.symm b := rfl

end SupMonoid
