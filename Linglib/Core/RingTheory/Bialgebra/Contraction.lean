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
* `contractAlong Δ f`: contraction of the left channel of a map `Δ` into a tensor product.
* `Derivation.ofContract`: contraction along an algebra map `Δ` with a left counit, as a derivation.
* `Bialgebra.IsDualPrimitive.derivation`: contraction with a dual primitive, as a derivation.

## Main results

* `Coalgebra.contract_counit`: the counit contracts to the identity.
* `contractAlong_map_comp`: contraction is natural in both channels.
* `contractAlong_mul`: a decomposition of a functional on products gives a product rule.
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

section Module

variable {R M N N' P P' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N'] [AddCommMonoid P] [Module R P]
  [AddCommMonoid P'] [Module R P']

/-- Contraction of the left channel of a map `Δ` into a tensor product with a functional:
`contractAlong Δ f a = (f ⊗ id) (Δ a)`. -/
noncomputable def contractAlong (Δ : M →ₗ[R] P ⊗[R] N) (f : P →ₗ[R] R) : M →ₗ[R] N :=
  (_root_.TensorProduct.lid R N).toLinearMap ∘ₗ f.rTensor N ∘ₗ Δ

theorem contractAlong_apply (Δ : M →ₗ[R] P ⊗[R] N) (f : P →ₗ[R] R) (a : M) :
    contractAlong Δ f a = _root_.TensorProduct.lid R N (f.rTensor N (Δ a)) := rfl

/-- Contraction is natural in both channels: contracting after a pair of maps is the right map
after contraction with the functional pulled back along the left map. -/
theorem contractAlong_map_comp (Δ : M →ₗ[R] P ⊗[R] N) (g : P →ₗ[R] P') (φ : N →ₗ[R] N')
    (f : P' →ₗ[R] R) :
    contractAlong (_root_.TensorProduct.map g φ ∘ₗ Δ) f = φ ∘ₗ contractAlong Δ (f ∘ₗ g) := by
  have h : (_root_.TensorProduct.lid R N').toLinearMap ∘ₗ f.rTensor N' ∘ₗ
      _root_.TensorProduct.map g φ =
      φ ∘ₗ (_root_.TensorProduct.lid R N).toLinearMap ∘ₗ (f ∘ₗ g).rTensor N :=
    _root_.TensorProduct.ext' fun a b ↦ by simp
  simp only [contractAlong, ← LinearMap.comp_assoc]
  rw [LinearMap.comp_assoc _ (f.rTensor N'), h]
  rfl

end Module

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Contraction along an algebra map turns a decomposition of a functional on products,
`f (a * b) = ∑ i, g i a * h i b`, into a product rule:
`f ⇀ (x * y) = ∑ i, (g i ⇀ x) * (h i ⇀ y)`. -/
theorem contractAlong_mul {ι : Type*} (Δ : A →ₐ[R] A ⊗[R] A) (s : Finset ι)
    (g h : ι → A →ₗ[R] R) (f : A →ₗ[R] R) (hf : ∀ a b, f (a * b) = ∑ i ∈ s, g i a * h i b)
    (x y : A) :
    contractAlong Δ.toLinearMap f (x * y) =
      ∑ i ∈ s, contractAlong Δ.toLinearMap (g i) x * contractAlong Δ.toLinearMap (h i) y := by
  have key (u v : A ⊗[R] A) :
      _root_.TensorProduct.lid R A (f.rTensor A (u * v)) =
        ∑ i ∈ s, _root_.TensorProduct.lid R A ((g i).rTensor A u) *
          _root_.TensorProduct.lid R A ((h i).rTensor A v) := by
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, Finset.sum_add_distrib]
    | tmul a b =>
      induction v using TensorProduct.inductionOn with
      | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, Finset.sum_add_distrib]
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul,
          _root_.TensorProduct.lid_tmul, hf, Finset.sum_smul, smul_mul_smul_comm]
  simpa [contractAlong_apply] using key (Δ x) (Δ y)

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
