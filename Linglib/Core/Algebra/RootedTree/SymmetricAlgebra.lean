/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra

/-!
# The Connes–Kreimer algebra as a symmetric algebra

A basis of a module `M` indexed by `T` gives an
[isomorphism](##SymmetricAlgebra.equivConnesKreimer) from the symmetric algebra on `M` to
`ConnesKreimer R T`, sending each basis vector to its tree, as `SymmetricAlgebra.equivMvPolynomial`
does for polynomials. It carries the comultiplication of the symmetric algebra, in which every
generator is primitive, to the primitive coproduct of the forests, and the counit to the counit.
On trees, where the primitive coproduct is the bialgebra structure of `WithCuts R emptyCuts`, it
is a [bialgebra isomorphism](##SymmetricAlgebra.bialgEquivConnesKreimer).

## References

* [grinberg-reiner-2020]
-/

@[expose] public section

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {T M : Type*} [AddCommMonoid M] [Module R M]

namespace SymmetricAlgebra

/-- A basis indexed by `T` gives an algebra isomorphism from the symmetric algebra to the
Connes–Kreimer algebra on `T`, replacing each basis vector with its tree. -/
noncomputable def equivConnesKreimer (b : Module.Basis T R M) :
    SymmetricAlgebra R M ≃ₐ[R] ConnesKreimer R T :=
  .ofAlgHom (lift (b.constr R ofTree)) (aeval fun t ↦ ι R M (b t))
    (algHom_ext_ofTree fun t ↦ by simp) (algHom_ext <| b.ext fun t ↦ by simp)

@[simp]
theorem equivConnesKreimer_ι_apply (b : Module.Basis T R M) (t : T) :
    equivConnesKreimer b (ι R M (b t)) = ofTree t :=
  (lift_ι_apply _ _).trans <| by simp

@[simp]
theorem equivConnesKreimer_symm_ofTree (b : Module.Basis T R M) (t : T) :
    (equivConnesKreimer b).symm (ofTree t) = ι R M (b t) :=
  (equivConnesKreimer b).toEquiv.symm_apply_eq.mpr (equivConnesKreimer_ι_apply b t).symm

end SymmetricAlgebra

/-- `ConnesKreimer R T` is the symmetric algebra on a module with basis `T`, each basis vector
going to its tree. -/
theorem IsSymmetricAlgebra.connesKreimer (b : Module.Basis T R M) :
    IsSymmetricAlgebra (b.constr R (ofTree (R := R))) :=
  (SymmetricAlgebra.equivConnesKreimer b).bijective

namespace ConnesKreimer

open SymmetricAlgebra

theorem counit_comp_equivConnesKreimer (b : Module.Basis T R M) :
    (counit (R := R)).comp (equivConnesKreimer b).toAlgHom =
      Bialgebra.counitAlgHom R (SymmetricAlgebra R M) :=
  SymmetricAlgebra.algHom_ext <| b.ext fun t ↦ by simp [algebraMapInv_ι]

theorem comulPrim_comp_equivConnesKreimer (b : Module.Basis T R M) :
    (comulPrim (R := R)).comp (equivConnesKreimer b).toAlgHom =
      (Algebra.TensorProduct.map (equivConnesKreimer b).toAlgHom
        (equivConnesKreimer b).toAlgHom).comp (Bialgebra.comulAlgHom R (SymmetricAlgebra R M)) :=
  SymmetricAlgebra.algHom_ext <| b.ext fun t ↦ by simp

end ConnesKreimer

namespace SymmetricAlgebra

variable {α : Type*}

/-- On trees the isomorphism with the symmetric algebra is one of bialgebras, the forests carrying
the coproduct in which every tree is primitive (Example 1.3.14 of [grinberg-reiner-2020]). -/
noncomputable def bialgEquivConnesKreimer (b : Module.Basis (UnorderedTree α) R M) :
    SymmetricAlgebra R M ≃ₐc[R] WithCuts R (emptyCuts (α := α)) :=
  .ofAlgEquiv (equivConnesKreimer b) (counit_comp_equivConnesKreimer b)
    (WithCuts.comulAlgHom_emptyCuts (R := R) ▸ (comulPrim_comp_equivConnesKreimer b).symm)

@[simp]
theorem bialgEquivConnesKreimer_apply (b : Module.Basis (UnorderedTree α) R M)
    (x : SymmetricAlgebra R M) : bialgEquivConnesKreimer b x = equivConnesKreimer b x :=
  rfl

end SymmetricAlgebra
