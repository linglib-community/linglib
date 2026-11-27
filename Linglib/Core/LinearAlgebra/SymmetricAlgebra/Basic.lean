/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The generators of the symmetric algebra

The map `SymmetricAlgebra.ι` from a module to its symmetric algebra is injective. As for
`TensorAlgebra.ι_leftInverse`, its left inverse `SymmetricAlgebra.ιInv` is the second component
of the algebra homomorphism into the trivial square-zero extension `R ⊕ M` that sends `m` to
`(0, m)`.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The left inverse of `SymmetricAlgebra.ι`. -/
def ιInv : SymmetricAlgebra R M →ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m ↦ rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp (lift (TrivSqZeroExt.inrHom R M)).toLinearMap

theorem ι_leftInverse : Function.LeftInverse ιInv (ι R M) := fun x ↦ by
  simp [ιInv]

theorem ι_injective : Function.Injective (ι R M) := ι_leftInverse.injective

variable (R) in
@[simp] theorem ι_inj (x y : M) : ι R M x = ι R M y ↔ x = y := ι_injective.eq_iff

end SymmetricAlgebra
