/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of the symmetric algebra

A derivation of the symmetric algebra of `M` is determined by its values on `M`
(`SymmetricAlgebra.derivation_ext`), and every linear map `f : M →ₗ[R] SymmetricAlgebra R M`
extends to one, `SymmetricAlgebra.mkDerivation f`, as `MvPolynomial.mkDerivation` does for
polynomials. On a product of elements of `M` it replaces each factor in turn by its value.

## Implementation notes

The derivation is the second component of the algebra homomorphism into the dual numbers
`a + bε` over the symmetric algebra that sends `m` to `ι m + f m ε`, which exists by the
universal property. Its first component is the identity, and the Leibniz rule is the formula for
the product of dual numbers.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A derivation of the symmetric algebra is determined by its values on the generators. -/
theorem derivation_ext {N : Type*} [AddCommMonoid N] [Module R N]
    [Module (SymmetricAlgebra R M) N] [IsScalarTower R (SymmetricAlgebra R M) N]
    {D₁ D₂ : Derivation R (SymmetricAlgebra R M) N} (h : ∀ m, D₁ (ι R M m) = D₂ (ι R M m)) :
    D₁ = D₂ :=
  Derivation.ext fun a ↦ by
    induction a using SymmetricAlgebra.induction with
    | algebraMap r => rw [Derivation.map_algebraMap, Derivation.map_algebraMap]
    | ι m => exact h m
    | mul a b ha hb => rw [Derivation.leibniz, Derivation.leibniz, ha, hb]
    | add a b ha hb => rw [map_add, map_add, ha, hb]

variable (f : M →ₗ[R] SymmetricAlgebra R M)

/-- The algebra homomorphism into the dual numbers that sends `m` to `ι m + f m ε`. -/
def toDualNumber : SymmetricAlgebra R M →ₐ[R] DualNumber (SymmetricAlgebra R M) :=
  lift
    { toFun := fun m ↦ TrivSqZeroExt.inl (ι R M m) + TrivSqZeroExt.inr (f m)
      map_add' := fun m n ↦ by ext <;> simp
      map_smul' := fun r m ↦ by ext <;> simp }

@[simp] theorem toDualNumber_ι (m : M) :
    toDualNumber f (ι R M m) = TrivSqZeroExt.inl (ι R M m) + TrivSqZeroExt.inr (f m) :=
  lift_ι_apply _ m

@[simp] theorem fst_toDualNumber (a : SymmetricAlgebra R M) : (toDualNumber f a).fst = a := by
  have h : (TrivSqZeroExt.fstHom R (SymmetricAlgebra R M) (SymmetricAlgebra R M)).comp
      (toDualNumber f) = AlgHom.id R _ := by
    ext m
    simp
  exact DFunLike.congr_fun h a

/-- The derivation of the symmetric algebra that takes the value `f m` on `ι m`. -/
def mkDerivation : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) where
  toFun a := (toDualNumber f a).snd
  map_add' a b := by rw [map_add, TrivSqZeroExt.snd_add]
  map_smul' r a := by rw [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
  map_one_eq_zero' := by
    change (toDualNumber f 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  leibniz' a b := by
    change (toDualNumber f (a * b)).snd = a • (toDualNumber f b).snd + b • (toDualNumber f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, fst_toDualNumber, fst_toDualNumber, smul_eq_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_comm b]

@[simp] theorem mkDerivation_ι (m : M) : mkDerivation f (ι R M m) = f m := by
  change (toDualNumber f (ι R M m)).snd = f m
  simp

end SymmetricAlgebra
