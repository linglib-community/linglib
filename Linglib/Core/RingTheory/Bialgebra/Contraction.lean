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
The derivation needs only that the comultiplication is an algebra map with a left counit, so it is
first constructed from those data, without coassociativity.

## Main definitions

* `Coalgebra.contract f`: contraction with the functional `f`.
* `Derivation.ofContract`: contraction along an algebra map `Δ` with a left counit, as a derivation.
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

section Explicit

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Contraction with a functional `f` along a comultiplication `Δ` that is an algebra map with a
left counit `ε`, as a derivation, when `f 1 = 0` and `f (a * b) = f a * ε b + ε a * f b`.
Coassociativity of `Δ` is not assumed. -/
noncomputable def Derivation.ofContract (Δ : A →ₐ[R] A ⊗[R] A) (ε : A →ₐ[R] R)
    (hε : ∀ a, ε.toLinearMap.rTensor A (Δ a) = 1 ⊗ₜ[R] a) (f : A →ₗ[R] R) (hf₁ : f 1 = 0)
    (hf : ∀ a b, f (a * b) = f a * ε b + ε a * f b) : Derivation R A A where
  toLinearMap := (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ f.rTensor A ∘ₗ Δ.toLinearMap
  map_one_eq_zero' := by
    simp [Algebra.TensorProduct.one_def, hf₁]
  leibniz' a b := by
    have key (u v : A ⊗[R] A) :
        _root_.TensorProduct.lid R A (f.rTensor A (u * v)) =
          _root_.TensorProduct.lid R A (ε.toLinearMap.rTensor A u) *
              _root_.TensorProduct.lid R A (f.rTensor A v) +
            _root_.TensorProduct.lid R A (ε.toLinearMap.rTensor A v) *
              _root_.TensorProduct.lid R A (f.rTensor A u) := by
      induction u using TensorProduct.inductionOn with
      | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, mul_add]; abel
      | tmul a b =>
        induction v using TensorProduct.inductionOn with
        | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, add_mul]; abel
        | tmul c d =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul,
            _root_.TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, hf, add_smul, mul_smul,
            smul_mul_smul_comm]
          rw [smul_comm (f a) (ε c), add_comm, mul_comm d b]
    have := key (Δ a) (Δ b)
    rw [← map_mul, hε, hε] at this
    simpa [add_comm] using this

@[simp] theorem Derivation.ofContract_apply (Δ : A →ₐ[R] A ⊗[R] A) (ε : A →ₐ[R] R)
    (hε : ∀ a, ε.toLinearMap.rTensor A (Δ a) = 1 ⊗ₜ[R] a) (f : A →ₗ[R] R) (hf₁ : f 1 = 0)
    (hf : ∀ a b, f (a * b) = f a * ε b + ε a * f b) (a : A) :
    Derivation.ofContract Δ ε hε f hf₁ hf a = _root_.TensorProduct.lid R A (f.rTensor A (Δ a)) :=
  rfl

end Explicit

namespace Bialgebra

open Coalgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]

/-- Contraction with a dual primitive is a derivation. -/
noncomputable def IsDualPrimitive.derivation {f : A →ₗ[R] R} (hf : IsDualPrimitive R f) :
    Derivation R A A :=
  Derivation.ofContract (comulAlgHom R A) (counitAlgHom R A) (fun a ↦ rTensor_counit_comul a) f
    hf.map_one_eq_zero hf.leibniz

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
