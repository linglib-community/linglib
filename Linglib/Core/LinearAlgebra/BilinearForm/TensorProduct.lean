/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Adjoint pairs for a tensor product of bilinear forms

If `f₁` and `g₁` are adjoint for a pair of bilinear forms and `f₂` and `g₂` are adjoint for another
pair, then `f₁ ⊗ f₂` and `g₁ ⊗ g₂` are adjoint for the tensor products of the forms. `[UPSTREAM]`
candidate; eventual mathlib home `Mathlib.LinearAlgebra.BilinearForm.TensorProduct`.
-/

public section

namespace LinearMap

open TensorProduct
open LinearMap (BilinForm)

variable {R M₁ M₂ N₁ N₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂]
  {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂} {C₁ : BilinForm R N₁} {C₂ : BilinForm R N₂}
  {f₁ : M₁ →ₗ[R] N₁} {g₁ : N₁ →ₗ[R] M₁} {f₂ : M₂ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] M₂}

/-- Adjoint pairs for two pairs of bilinear forms tensor to an adjoint pair for the tensor
products of the forms. -/
theorem IsAdjointPair.tmul (h₁ : IsAdjointPair B₁ C₁ f₁ g₁) (h₂ : IsAdjointPair B₂ C₂ f₂ g₂) :
    IsAdjointPair (B₁.tmul B₂) (C₁.tmul C₂) (TensorProduct.map f₁ f₂) (TensorProduct.map g₁ g₂) := by
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul m₁ m₂ =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul n₁ n₂ => simp only [map_tmul, BilinForm.tensorDistrib_tmul, h₁ m₁ n₁, h₂ m₂ n₂]

end LinearMap
