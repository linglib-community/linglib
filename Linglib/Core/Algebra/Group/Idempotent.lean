/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Idempotent`, with the `MulZeroClass` lemmas in
`Mathlib.Algebra.GroupWithZero.Basic`.
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Left and right zeros

An element `a` of a magma is a *left zero* when `a * b = a` for every `b`, and a *right zero* when
`b * a = a` for every `b`. A one-sided zero is idempotent, and `MulOpposite` exchanges the two
notions. In a semigroup the left zeros form a left ideal and the right zeros a right ideal.

## Main definitions

* `IsLeftZero`, `IsRightZero`: the left and right zeros.

## Main results

* `IsLeftZero.mul_left`, `IsRightZero.mul_right`: the ideal property.
* `IsLeftZero.map_of_surjective`, `IsLeftZero.of_map` and their mirrors: transport along
  surjective and injective homomorphisms.

## References

* [pin-mfa]
-/

@[expose] public section

variable {M N F : Type*}

section Mul
variable [Mul M] {a : M}

/-- An element `a` is a *left zero* if `a * b = a` for every `b`. -/
def IsLeftZero (a : M) : Prop := ∀ b, a * b = a

/-- An element `a` is a *right zero* if `b * a = a` for every `b`. -/
def IsRightZero (a : M) : Prop := ∀ b, b * a = a

theorem isLeftZero_iff : IsLeftZero a ↔ ∀ b, a * b = a := Iff.rfl

theorem isRightZero_iff : IsRightZero a ↔ ∀ b, b * a = a := Iff.rfl

@[simp] theorem isLeftZero_op : IsLeftZero (MulOpposite.op a) ↔ IsRightZero a :=
  MulOpposite.op_surjective.forall.trans <| forall_congr' fun _ ↦ MulOpposite.op_inj

@[simp] theorem isRightZero_op : IsRightZero (MulOpposite.op a) ↔ IsLeftZero a :=
  MulOpposite.op_surjective.forall.trans <| forall_congr' fun _ ↦ MulOpposite.op_inj

theorem IsLeftZero.isIdempotentElem (h : IsLeftZero a) : IsIdempotentElem a := h a

theorem IsRightZero.isIdempotentElem (h : IsRightZero a) : IsIdempotentElem a := h a

section Hom
variable [Mul N] [FunLike F M N] [MulHomClass F M N] {f : F}

theorem IsLeftZero.map_of_surjective (h : IsLeftZero a) (hf : Function.Surjective f) :
    IsLeftZero (f a) :=
  hf.forall.2 fun b ↦ by rw [← map_mul, h]

theorem IsRightZero.map_of_surjective (h : IsRightZero a) (hf : Function.Surjective f) :
    IsRightZero (f a) :=
  hf.forall.2 fun b ↦ by rw [← map_mul, h]

theorem IsLeftZero.of_map (h : IsLeftZero (f a)) (hf : Function.Injective f) : IsLeftZero a :=
  fun b ↦ hf <| by rw [map_mul, h]

theorem IsRightZero.of_map (h : IsRightZero (f a)) (hf : Function.Injective f) :
    IsRightZero a :=
  fun b ↦ hf <| by rw [map_mul, h]

end Hom

end Mul

section Semigroup
variable [Semigroup M] {a : M}

theorem IsLeftZero.mul_left (h : IsLeftZero a) (b : M) : IsLeftZero (b * a) :=
  fun c ↦ by rw [mul_assoc, h]

theorem IsRightZero.mul_right (h : IsRightZero a) (b : M) : IsRightZero (a * b) :=
  fun c ↦ by rw [← mul_assoc, h]

end Semigroup

section MulZeroClass
variable [MulZeroClass M]

@[simp] theorem isLeftZero_zero : IsLeftZero (0 : M) := zero_mul

@[simp] theorem isRightZero_zero : IsRightZero (0 : M) := mul_zero

end MulZeroClass
