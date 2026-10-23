/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Multiset
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Algebra.RootedTree.Homogeneous
public import Linglib.Core.Algebra.RootedTree.SymmetricAlgebra
public import Linglib.Core.Data.Multiset.Antidiagonal
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra

/-!
# The primitive coproduct on the Connes–Kreimer algebra

The primitive coproduct `Δ_P(t) = t ⊗ 1 + 1 ⊗ t` on `ConnesKreimer R T`, extended
multiplicatively, sums `A ⊗ B` over the splittings `F = A + B` of a forest. It is the coproduct
of the symmetric algebra on the trees (Grinberg and Reiner, Example 1.3.14), unlike the
admissible-cut coproducts of the sibling files.

## Main declarations

* `ConnesKreimer.comulPrim`: the primitive coproduct, as an algebra homomorphism.
* `ConnesKreimer.comulPrim_of'`: `Δ_P(F) = ∑_{A + B = F} A ⊗ B`.
* `ConnesKreimer.comulAlgHomNG_emptyCuts`: `Δ_P` is the admissible-cut coproduct whose only cut
  is the empty one.
* `ConnesKreimer.rTensor_homogeneousComponent_comulPrim_of'`: the terms whose left factor has
  `k` trees are indexed by the `k`-tree subforests.
* `ConnesKreimer.comulPrim_coassoc`, `ConnesKreimer.rTensor_counit_comp_comulPrim`,
  `ConnesKreimer.lTensor_counit_comp_comulPrim`, `ConnesKreimer.comm_comp_comulPrim`: the
  coalgebra laws and cocommutativity, in the shape of `Bialgebra.ofAlgHom`.
* `ConnesKreimer.comulPrim_comp_equiv`: along `IsSymmetricAlgebra.connesKreimer`, `Δ_P` is the
  comultiplication of `SymmetricAlgebra.instBialgebra`.

## Implementation notes

`Δ_P` is not a `Bialgebra` instance: the carrier already carries the admissible-cut
`Bialgebra` (`HopfAlgebra.lean`), so `Δ_P` is an algebra homomorphism with its laws stated
separately.

## References

* [grinberg-reiner-2020]
-/

@[expose] public section

namespace ConnesKreimer

open UnorderedTree
open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {T : Type*}

/-- The primitive coproduct `Δ_P` is the algebra homomorphism under which every tree is
primitive, `Δ_P(t) = t ⊗ 1 + 1 ⊗ t`. -/
noncomputable def comulPrim : ConnesKreimer R T →ₐ[R] ConnesKreimer R T ⊗[R] ConnesKreimer R T :=
  aeval fun t ↦ ofTree t ⊗ₜ[R] (1 : ConnesKreimer R T) + (1 : ConnesKreimer R T) ⊗ₜ[R] ofTree t

@[simp] theorem comulPrim_ofTree (t : T) :
    comulPrim (R := R) (ofTree t) =
      ofTree t ⊗ₜ[R] (1 : ConnesKreimer R T) + (1 : ConnesKreimer R T) ⊗ₜ[R] ofTree t :=
  aeval_ofTree _ t

theorem comulPrim_unique
    (φ : ConnesKreimer R T →ₐ[R] ConnesKreimer R T ⊗[R] ConnesKreimer R T)
    (h : ∀ t, φ (ofTree t) =
      ofTree t ⊗ₜ[R] (1 : ConnesKreimer R T) + (1 : ConnesKreimer R T) ⊗ₜ[R] ofTree t) :
    φ = comulPrim :=
  algHom_ext_ofTree fun t ↦ by rw [h, comulPrim_ofTree]

/-- The admissible-cut coproduct at the empty-cut enumeration is primitive. -/
theorem comulAlgHomNG_emptyCuts {α : Type*} :
    comulAlgHomNG (R := R) (α := α) emptyCuts = comulPrim :=
  comulPrim_unique _ fun t ↦ by simp [comulTreeNG, emptyCuts]

private theorem prod_map_tmul_one (A : Forest T) :
    (A.map fun t ↦ (ofTree t : ConnesKreimer R T) ⊗ₜ[R] (1 : ConnesKreimer R T)).prod =
      of' A ⊗ₜ[R] (1 : ConnesKreimer R T) := by
  induction A using Multiset.induction with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, of'_zero, Algebra.TensorProduct.one_def]
  | cons t A ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Algebra.TensorProduct.tmul_mul_tmul,
      of'_cons, one_mul]

private theorem prod_map_one_tmul (B : Forest T) :
    (B.map fun t ↦ (1 : ConnesKreimer R T) ⊗ₜ[R] (ofTree t : ConnesKreimer R T)).prod =
      (1 : ConnesKreimer R T) ⊗ₜ[R] of' B := by
  induction B using Multiset.induction with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, of'_zero, Algebra.TensorProduct.one_def]
  | cons t B ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Algebra.TensorProduct.tmul_mul_tmul,
      of'_cons, one_mul]

/-- `Δ_P` sums `A ⊗ B` over the splittings `F = A + B`, counted with multiplicity. -/
theorem comulPrim_of' (F : Forest T) :
    comulPrim (R := R) (of' F) =
      (F.antidiagonal.map fun p ↦ (of' p.1 : ConnesKreimer R T) ⊗ₜ[R] of' p.2).sum := by
  rw [comulPrim, aeval_of', Multiset.prod_map_add]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  rw [prod_map_tmul_one, prod_map_one_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The terms of `Δ_P(F)` whose left factor has `k` trees sum `A ⊗ (F - A)` over the `k`-tree
subforests `A` of `F`. -/
theorem rTensor_homogeneousComponent_comulPrim_of' [DecidableEq T] (k : ℕ) (F : Forest T) :
    (homogeneousComponent k).rTensor _ (comulPrim (R := R) (of' F)) =
      ((F.powersetCard k).map fun A ↦ (of' A : ConnesKreimer R T) ⊗ₜ[R] of' (F - A)).sum := by
  have h : (F.powersetCard k).map (fun A ↦ (of' A : ConnesKreimer R T) ⊗ₜ[R] of' (F - A)) =
      (F.antidiagonal.filter fun p ↦ p.1.card = k).map
        fun p ↦ (of' p.1 : ConnesKreimer R T) ⊗ₜ[R] (of' p.2 : ConnesKreimer R T) := by
    rw [Multiset.filter_card_fst_eq_antidiagonal, Multiset.map_map]
    rfl
  rw [h, Multiset.sum_map_filter, comulPrim_of', map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  simp only [Function.comp_apply, LinearMap.rTensor_tmul, homogeneousComponent_of']
  split_ifs <;> simp

theorem comulPrim_coassoc :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R T) (ConnesKreimer R T)
        (ConnesKreimer R T)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulPrim (R := R) (T := T)) (.id R _)).comp comulPrim) =
    (Algebra.TensorProduct.map (.id R _) (comulPrim (R := R) (T := T))).comp comulPrim := by
  ext t
  simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

theorem rTensor_counit_comp_comulPrim :
    (Algebra.TensorProduct.map counit (.id R _)).comp (comulPrim (R := R) (T := T)) =
      (Algebra.TensorProduct.lid R (ConnesKreimer R T)).symm := by
  ext t
  simp

theorem lTensor_counit_comp_comulPrim :
    (Algebra.TensorProduct.map (.id R _) counit).comp (comulPrim (R := R) (T := T)) =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R T)).symm := by
  ext t
  simp

theorem comm_comp_comulPrim :
    (Algebra.TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T)).toAlgHom.comp
      (comulPrim (R := R) (T := T)) = comulPrim := by
  ext t
  simp [add_comm]

/-- Along the identification of `ConnesKreimer R T` with the symmetric algebra on a module with
basis `T`, `Δ_P` is the comultiplication of the symmetric algebra. -/
theorem comulPrim_comp_equiv {M : Type*} [AddCommMonoid M] [Module R M] (b : Module.Basis T R M) :
    (comulPrim (R := R)).comp (IsSymmetricAlgebra.connesKreimer b).equiv.toAlgHom =
      (Algebra.TensorProduct.map (IsSymmetricAlgebra.connesKreimer b).equiv.toAlgHom
        (IsSymmetricAlgebra.connesKreimer b).equiv.toAlgHom).comp
        (Bialgebra.comulAlgHom R (SymmetricAlgebra R M)) := by
  refine SymmetricAlgebra.algHom_ext <| b.ext fun t ↦ ?_
  simp

end ConnesKreimer
