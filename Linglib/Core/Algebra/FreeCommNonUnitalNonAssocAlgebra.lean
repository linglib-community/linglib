/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.FreeCommMagma
public import Mathlib.Algebra.FreeNonUnitalNonAssocAlgebra

/-!
# Free commutative non-associative algebras

Given a commutative semiring `R` and a type `X`, we construct the free commutative, non-unital,
non-associative algebra on `X` with coefficients in `R`, together with its universal property. It is
the magma algebra of the free commutative magma on `X`, beside mathlib's
`FreeNonUnitalNonAssocAlgebra`, the magma algebra of the free magma, of which it is the quotient by
commutativity.

A typical element is an `R`-linear combination of nonempty formal commutative, non-associative
products of elements of `X`, that is, of binary unordered rooted trees with leaves in `X`.

## Main definitions

* `MonoidAlgebra.nonUnitalNonAssocCommSemiring`: the magma algebra of a commutative magma is
  commutative.
* `FreeCommNonUnitalNonAssocAlgebra`: the algebra.
* `FreeCommNonUnitalNonAssocAlgebra.of`: the embedding of the generators.
* `FreeCommNonUnitalNonAssocAlgebra.lift`: the universal property.
* `FreeNonUnitalNonAssocAlgebra.toComm`: the quotient map from the free non-associative algebra.

## Implementation notes

The definitions follow `Mathlib/Algebra/FreeNonUnitalNonAssocAlgebra.lean` line by line, with
`FreeCommMagma.lift` in place of `FreeMagma.lift`. `[UPSTREAM]` candidate.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra

namespace MonoidAlgebra

variable {R M : Type*} [CommSemiring R] [CommMagma M]

instance nonUnitalNonAssocCommSemiring : NonUnitalNonAssocCommSemiring R[M] where
  mul_comm x y := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => rw [zero_mul, mul_zero]
    | add f g hf hg => rw [add_mul, mul_add, hf, hg]
    | single a b =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => rw [zero_mul, mul_zero]
      | add f g hf hg => rw [add_mul, mul_add, hf, hg]
      | single c d => rw [single_mul_single, single_mul_single, mul_comm a, mul_comm b]

end MonoidAlgebra

variable (R X A : Type*) [CommSemiring R]

/-- The free commutative, non-unital, non-associative `R`-algebra on `X`, the magma algebra of the
free commutative magma on `X`. -/
abbrev FreeCommNonUnitalNonAssocAlgebra := R[FreeCommMagma X]

namespace FreeCommNonUnitalNonAssocAlgebra

variable {X A}

/-- The embedding of `X` into the free commutative algebra with coefficients in `R`. -/
def of : X → FreeCommNonUnitalNonAssocAlgebra R X :=
  MonoidAlgebra.ofMagma R _ ∘ FreeCommMagma.of

variable [NonUnitalNonAssocCommSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- The functor `X ↦ FreeCommNonUnitalNonAssocAlgebra R X` from the category of types to the
category of commutative non-unital, non-associative algebras over `R` is adjoint to the forgetful
functor in the other direction. -/
def lift : (X → A) ≃ (FreeCommNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :=
  FreeCommMagma.lift.trans (MonoidAlgebra.liftMagma R)

@[simp] theorem lift_symm_apply (F : FreeCommNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    (lift R).symm F = F ∘ of R := rfl

@[simp] theorem of_comp_lift (f : X → A) : lift R f ∘ of R = f := (lift R).left_inv f

@[simp] theorem lift_unique (f : X → A) (F : FreeCommNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    F ∘ of R = f ↔ F = lift R f :=
  (lift R).symm_apply_eq

@[simp] theorem lift_of_apply (f : X → A) (x : X) : lift R f (of R x) = f x :=
  congrFun (of_comp_lift R f) x

@[simp] theorem lift_comp_of (F : FreeCommNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    lift R (F ∘ of R) = F :=
  (lift R).apply_symm_apply F

@[ext] theorem hom_ext {F₁ F₂ : FreeCommNonUnitalNonAssocAlgebra R X →ₙₐ[R] A}
    (h : ∀ x, F₁ (of R x) = F₂ (of R x)) : F₁ = F₂ :=
  (lift R).symm.injective <| funext h

end FreeCommNonUnitalNonAssocAlgebra

namespace FreeNonUnitalNonAssocAlgebra

variable {X}

/-- The quotient of the free non-associative algebra by commutativity, forgetting the order of the
factors of every product. -/
def toComm : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] FreeCommNonUnitalNonAssocAlgebra R X :=
  MonoidAlgebra.mapDomainNonUnitalAlgHom R R FreeMagma.toFreeCommMagma

@[simp] theorem toComm_single (p : FreeMagma X) (r : R) :
    toComm R (MonoidAlgebra.single p r) = MonoidAlgebra.single p.toFreeCommMagma r :=
  MonoidAlgebra.mapDomain_single

@[simp] theorem toComm_of (x : X) : toComm R (of R x) = FreeCommNonUnitalNonAssocAlgebra.of R x :=
  MonoidAlgebra.mapDomain_single

end FreeNonUnitalNonAssocAlgebra
