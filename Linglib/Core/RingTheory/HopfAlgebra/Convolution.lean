/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Convolution inverses in a commutative Hopf algebra

Let `A` be a commutative Hopf algebra with antipode `S`. For every algebra map `f` from `A` into a
commutative algebra, `f ∘ S` is a left convolution inverse of `f`; mathlib's convolution group
`AlgHom.convGroup` states this only when the target is itself a bialgebra. In the convolution group
`WithConv (A →ₐ[R] A)` the antipode `S` is the inverse of the identity, `S ∘ S` is the inverse of
`S`, and so `S ∘ S` is the identity.

## Main results

* `AlgHom.comp_antipode_cancel`: `(f ∘ S) ⋆ f = 1`.
* `HopfAlgebra.antipode_antipode`: the antipode is an involution.

[UPSTREAM] Belongs in `Mathlib/RingTheory/HopfAlgebra/Convolution.lean`, settling the TODO on
commutative Hopf algebras in `Mathlib/RingTheory/HopfAlgebra/Basic.lean`.

## References

* [grinberg-reiner-2020]
-/

@[expose] public section

open WithConv

variable {R A C : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

/-- For an algebra map `f` from a commutative Hopf algebra into a commutative algebra, `f ∘ S` is
a left convolution inverse of `f`: the antipode law `S ⋆ id = 1` transported along `f`. -/
theorem AlgHom.comp_antipode_cancel [CommSemiring C] [Algebra R C] (f : A →ₐ[R] C) :
    toConv (f.comp (HopfAlgebra.antipodeAlgHom R A)) * toConv f = 1 := by
  have h := comp_convMul_distrib f (toConv (HopfAlgebra.antipodeAlgHom R A)) (toConv (.id R A))
  rw [antipode_id_cancel, comp_id] at h
  refine ofConv_injective ?_
  rw [← h]
  simp only [convOne_def, ofConv_toConv, ← comp_assoc,
    Subsingleton.elim (f.comp (Algebra.ofId R A)) (Algebra.ofId R C)]

namespace HopfAlgebra

theorem antipodeAlgHom_comp_antipodeAlgHom :
    (antipodeAlgHom R A).comp (antipodeAlgHom R A) = .id R A :=
  congr(ofConv $(inv_inv (toConv (AlgHom.id R A))))

/-- See Corollary 1.4.12 in [grinberg-reiner-2020]. -/
@[simp]
theorem antipode_antipode (a : A) : antipode R (antipode R a) = a :=
  congr($antipodeAlgHom_comp_antipodeAlgHom a)

theorem antipode_involutive : Function.Involutive (antipode R : A → A) :=
  antipode_antipode

end HopfAlgebra
