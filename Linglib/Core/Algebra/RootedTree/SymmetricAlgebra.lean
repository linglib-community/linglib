/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The Connes–Kreimer algebra is a symmetric algebra

As an algebra, `ConnesKreimer R T` is the symmetric algebra on the free module with basis `T`,
as `MvPolynomial` is (`IsSymmetricAlgebra.mvPolynomial`). The carrier stays a separate type: it
carries the admissible-cut `Bialgebra`, while `SymmetricAlgebra` carries the one in which every
generator is primitive.

## Main results

* `IsSymmetricAlgebra.connesKreimer`: for a basis `b` of `M` indexed by `T`, the linear map
  sending `b t` to the tree `t` exhibits `ConnesKreimer R T` as the symmetric algebra on `M`.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

variable {R : Type*} [CommSemiring R] {T M : Type*} [AddCommMonoid M] [Module R M]

/-- `ConnesKreimer R T` is the symmetric algebra on a module with basis `T`, each basis vector
going to its tree. -/
theorem IsSymmetricAlgebra.connesKreimer (b : Module.Basis T R M) :
    IsSymmetricAlgebra (b.constr R (ConnesKreimer.ofTree (R := R))) :=
  (AlgEquiv.ofAlgHom (SymmetricAlgebra.lift (b.constr R ConnesKreimer.ofTree))
    (ConnesKreimer.aeval fun t ↦ SymmetricAlgebra.ι R M (b t))
    (ConnesKreimer.algHom_ext_ofTree fun t ↦ by simp)
    (SymmetricAlgebra.algHom_ext <| b.ext fun t ↦ by simp)).bijective
