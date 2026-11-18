/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Algebra.RootedTree.Homogeneous
public import Linglib.Core.Data.Multiset.Antidiagonal

/-!
# The primitive coproduct on the Connes–Kreimer algebra

The primitive coproduct `Δ_P(t) = t ⊗ 1 + 1 ⊗ t` on `ConnesKreimer R T`, extended
multiplicatively, sums `A ⊗ B` over the splittings `F = A + B` of a forest. It is the coproduct
of the symmetric algebra on the trees, unlike the admissible-cut coproducts of the sibling files.

## Main declarations

* `ConnesKreimer.comulPrim`: the primitive coproduct, as an algebra homomorphism.
* `ConnesKreimer.comulPrim_of'`: `Δ_P(F) = ∑_{A + B = F} A ⊗ B`.
* `ConnesKreimer.comulOfCuts_emptyCuts`: `Δ_P` is the admissible-cut coproduct whose only cut
  is the empty one.
* `ConnesKreimer.rTensor_homogeneousComponent_comulPrim_of'`: the terms whose left factor has
  `k` trees are indexed by the `k`-tree subforests.
* `ConnesKreimer.comm_comp_comulPrim`: `Δ_P` is cocommutative.
* `ConnesKreimer.WithCuts.comulAlgHom_emptyCuts`: on trees, `Δ_P` is the comultiplication of the
  bialgebra `WithCuts R emptyCuts`.

## Implementation notes

`Δ_P` is not a `Bialgebra` instance on `ConnesKreimer R T`: on trees that carrier already carries
the Connes–Kreimer `Bialgebra` (`ConnesKreimer.instBialgebra`). On trees the synonym
`WithCuts R emptyCuts` carries `Δ_P` as its `Bialgebra`.

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
theorem comulOfCuts_emptyCuts {α : Type*} :
    comulOfCuts (R := R) (α := α) emptyCuts = comulPrim :=
  comulPrim_unique _ fun t ↦ by simp [comulTreeOfCuts, emptyCuts]

/-- `Δ_P` sums `A ⊗ B` over the splittings `F = A + B`, counted with multiplicity. -/
theorem comulPrim_of' (F : Forest T) :
    comulPrim (R := R) (of' F) =
      (F.antidiagonal.map fun p ↦ (of' p.1 : ConnesKreimer R T) ⊗ₜ[R] of' p.2).sum := by
  rw [comulPrim, aeval_of', Multiset.prod_map_add]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  rw [← mul_one (of' p.1), ← one_mul (of' p.2), ← Algebra.TensorProduct.tmul_mul_tmul,
    ← prod_map_ofTree, ← prod_map_ofTree, ← Algebra.TensorProduct.includeLeft_apply (S := R),
    ← Algebra.TensorProduct.includeRight_apply, map_multiset_prod, map_multiset_prod,
    Multiset.map_map, Multiset.map_map]
  rfl

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

theorem comm_comp_comulPrim :
    (Algebra.TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T)).toAlgHom.comp
      (comulPrim (R := R) (T := T)) = comulPrim := by
  ext t
  simp [add_comm]

/-! ### The primitive bialgebra

On trees the primitive coproduct is the admissible-cut coproduct at the empty-cut enumeration, so
`WithCuts R emptyCuts` carries it as a `Bialgebra`. -/

section WithCuts
variable {α : Type*}

instance : IsBialgebraCuts (emptyCuts (α := α)) where
  doubleCutsCrown_eq T := by
    have h : Multiset.antidiagonal ({T} : Multiset (UnorderedTree α)) = {(0, {T}), ({T}, 0)} := by
      rw [← Multiset.cons_zero T, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]; rfl
    simp only [doubleCutsCrown, doubleCutsTrunk, treeCuts, forestCuts_emptyCuts, emptyCuts]
    simp [h]
    rw [← Multiset.singleton_add, ← Multiset.singleton_add, ← Multiset.singleton_add,
      ← Multiset.singleton_add]
    abel
  filter_card_eq_zero T := by simp [emptyCuts, Multiset.filter_singleton]

theorem WithCuts.comulAlgHom_emptyCuts :
    Bialgebra.comulAlgHom R (WithCuts R (emptyCuts (α := α))) = comulPrim :=
  comulOfCuts_emptyCuts

theorem WithCuts.counitAlgHom_emptyCuts :
    Bialgebra.counitAlgHom R (WithCuts R (emptyCuts (α := α))) = counit :=
  rfl

instance : Coalgebra.IsCocomm R (WithCuts R (emptyCuts (α := α))) where
  comm_comp_comul := congr(($comm_comp_comulPrim).toLinearMap)

end WithCuts

end ConnesKreimer
