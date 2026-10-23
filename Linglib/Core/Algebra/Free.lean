/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# Bracketings in a free magma

An element of a free magma is a bracketing of a nonempty list of generators. This file singles
out the left combs, the bracketings `((a * b) * c) * d` in which every product has a generator
as its right factor, and shows that a homomorphism into a semigroup depends on the list of
generators alone.

## Main definitions

* `FreeMagma.IsLeftComb`: the element is a left comb.

## Main results

* `FreeMagma.isLeftComb_foldl_mul_of`: multiplying on the right by generators preserves and
  reflects being a left comb.
* `FreeMagma.toList_lift_foldl_mul_of`: multiplying on the right by generators appends them to
  the list of generators.
* `FreeMagma.lift_eq_lift_of_lift_of_eq`: a homomorphism into a semigroup takes two elements
  with the same generators in the same order to the same value.
-/

@[expose] public section

namespace FreeMagma

variable {α : Type*}

/-- An element of a free magma is a left comb when every product in it has a generator as its
right factor. -/
def IsLeftComb : FreeMagma α → Prop
  | of _ => True
  | mul x (of _) => IsLeftComb x
  | mul _ (mul _ _) => False

instance decidableIsLeftComb : (x : FreeMagma α) → Decidable (IsLeftComb x)
  | of _ => isTrue trivial
  | mul x (of _) => decidableIsLeftComb x
  | mul _ (mul _ _) => isFalse id

@[simp] theorem isLeftComb_of (a : α) : IsLeftComb (of a) := trivial

@[simp] theorem isLeftComb_mul_of (x : FreeMagma α) (a : α) :
    IsLeftComb (x * of a) ↔ IsLeftComb x := Iff.rfl

@[simp] theorem not_isLeftComb_mul_mul (x y z : FreeMagma α) : ¬ IsLeftComb (x * (y * z)) := id

theorem isLeftComb_foldl_mul_of (x : FreeMagma α) (l : List α) :
    IsLeftComb (l.foldl (· * of ·) x) ↔ IsLeftComb x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem toList_lift_foldl_mul_of (x : FreeMagma α) (l : List α) :
    (lift FreeMonoid.of (l.foldl (· * of ·) x)).toList = (lift FreeMonoid.of x).toList ++ l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih]

section Semigroup

variable {β : Type*} [Semigroup β]

theorem lift_eq_lift_toFreeSemigroup (f : α → β) (x : FreeMagma α) :
    lift f x = FreeSemigroup.lift f (toFreeSemigroup x) := by
  induction x using FreeMagma.recOnMul with
  | ih1 a => rfl
  | ih2 x y hx hy => simp [hx, hy]

theorem lift_of_eq_toFreeMonoid (x : FreeMagma α) :
    lift FreeMonoid.of x = (toFreeSemigroup x).toFreeMonoid :=
  lift_eq_lift_toFreeSemigroup _ x

/-- A homomorphism from a free magma to a semigroup does not see the bracketing: it takes two
elements with the same generators in the same order to the same value. -/
theorem lift_eq_lift_of_lift_of_eq (f : α → β) {x y : FreeMagma α}
    (h : lift FreeMonoid.of x = lift FreeMonoid.of y) : lift f x = lift f y := by
  have : toFreeSemigroup x = toFreeSemigroup y :=
    FreeSemigroup.toFreeMonoid_injective (by simpa only [lift_of_eq_toFreeMonoid] using h)
  rw [lift_eq_lift_toFreeSemigroup, lift_eq_lift_toFreeSemigroup, this]

end Semigroup

end FreeMagma
