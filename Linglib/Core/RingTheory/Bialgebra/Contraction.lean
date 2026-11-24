/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Contraction of a coalgebra with a functional

A linear functional `f` on a coalgebra `A` acts on `A` by contracting the left channel of the
comultiplication: `contract f a = (f ⊗ id) (Δ a)`, in Sweedler notation `∑ f a₍₁₎ • a₍₂₎`. The
counit acts as the identity.

On a commutative bialgebra, contraction with a functional that is primitive in the dual is a
derivation of the algebra, and conversely the counit after a derivation is primitive in the dual.

## Main definitions

* `Coalgebra.contract f`: contraction with the functional `f`.
* `Bialgebra.IsDualPrimitive.derivation`: contraction with a dual primitive, as a derivation.

## Main results

* `Coalgebra.contract_counit`: the counit contracts to the identity.
* `Bialgebra.isDualPrimitive_counit_comp`: the counit after a derivation is a dual primitive.

## Implementation notes

`Bialgebra.IsDualPrimitive.derivation` is a bundled `Derivation`, so the product rule and the rest
of the derivation API apply to contractions. `[UPSTREAM]` candidate.

## References

* [radford-2012]
-/

@[expose] public section

open scoped TensorProduct

namespace Coalgebra

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-- Contraction of the left channel of the comultiplication with a functional:
`contract f a = (f ⊗ id) (Δ a)`. -/
noncomputable def contract (f : A →ₗ[R] R) : A →ₗ[R] A :=
  (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ f.rTensor A ∘ₗ comul

theorem contract_apply (f : A →ₗ[R] R) (a : A) :
    contract f a = _root_.TensorProduct.lid R A (f.rTensor A (comul a)) := rfl

@[simp] theorem contract_counit : contract (counit : A →ₗ[R] R) = LinearMap.id := by
  ext a
  simp [contract_apply, rTensor_counit_comul]

end Coalgebra

namespace Bialgebra

open Coalgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]

/-- Contraction with a dual primitive is a derivation. -/
noncomputable def IsDualPrimitive.derivation {f : A →ₗ[R] R} (hf : IsDualPrimitive R f) :
    Derivation R A A where
  toLinearMap := contract f
  map_one_eq_zero' := by
    simp [contract_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def, hf.map_one_eq_zero]
  leibniz' a b := by
    have key (u v : A ⊗[R] A) :
        _root_.TensorProduct.lid R A (f.rTensor A (u * v)) =
          _root_.TensorProduct.lid R A (counit.rTensor A u) *
              _root_.TensorProduct.lid R A (f.rTensor A v) +
            _root_.TensorProduct.lid R A (counit.rTensor A v) *
              _root_.TensorProduct.lid R A (f.rTensor A u) := by
      induction u using TensorProduct.inductionOn with
      | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, mul_add]; abel
      | tmul a b =>
        induction v using TensorProduct.inductionOn with
        | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, add_mul]; abel
        | tmul c d =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul,
            _root_.TensorProduct.lid_tmul, hf.leibniz, add_smul, mul_smul, smul_mul_smul_comm]
          rw [smul_comm (f a) (counit c), add_comm, mul_comm d b]
    have := key (comul a) (comul b)
    rw [← comul_mul, rTensor_counit_comul, rTensor_counit_comul] at this
    simpa [contract_apply, add_comm] using this

@[simp] theorem IsDualPrimitive.derivation_apply {f : A →ₗ[R] R} (hf : IsDualPrimitive R f)
    (a : A) : hf.derivation a = contract f a := rfl

/-- The counit after a derivation is primitive in the dual. -/
theorem isDualPrimitive_counit_comp (D : Derivation R A A) :
    IsDualPrimitive R ((counit : A →ₗ[R] R) ∘ₗ (D : A →ₗ[R] A)) where
  map_one_eq_zero := by simp
  leibniz a b := by
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, Derivation.leibniz, map_add, smul_eq_mul,
      counit_mul]
    ring

end Bialgebra
