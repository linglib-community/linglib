/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The Connes–Kreimer coproduct Δ^ρ

The Connes–Kreimer coproduct on unordered rooted trees, summing over admissible cuts, which leave
nothing in place of the subtrees they remove. Grafting `B⁺_a` is a Hochschild 1-cocycle for it, and
coassociativity follows from the cocycle by induction on trees. The counit laws are those of the
generic coproduct, since the empty cut is the only admissible cut with an empty crown.

## Main definitions

* `ConnesKreimer.comulAlgHom`: the Δ^ρ coproduct, as the generic admissible-cut coproduct
  (`Coproduct/WithCuts.lean`) at the enumeration `admissibleCuts`.
* `ConnesKreimer.bPlus`: grafting `B⁺_a` as a linear map.

## Main results

* `ConnesKreimer.comulAlgHom_bPlus_cocycle`: the Hochschild 1-cocycle law
  `Δ^ρ (B⁺_a x) = B⁺_a x ⊗ 1 + (id ⊗ B⁺_a) (Δ^ρ x)`.
* `ConnesKreimer.comulAlgHom_coassoc_algHom`: coassociativity.
* `ConnesKreimer.instBialgebra`: the Δ^ρ `Bialgebra`, over any `CommSemiring`; the admissible
  cuts are admissible (`ConnesKreimer.instIsBialgebraCutsAdmissibleCuts`).

## Implementation notes

`B⁺_a` takes the children as a multiset, `Multiset (UnorderedTree α) → UnorderedTree α`; on planar
trees it would need a canonical order of the children, so the cocycle and everything after it live
at the `UnorderedTree` level.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
* [grinberg-reiner-2020]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### The coproduct -/

/-- The Connes–Kreimer coproduct Δ^ρ as an algebra homomorphism, which is `comulOfCuts` at the
admissible cuts. -/
noncomputable def comulAlgHom :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulOfCuts admissibleCuts

@[simp] theorem comulAlgHom_apply_of' (F : Forest (UnorderedTree α)) :
    comulAlgHom (R := R) (α := α) (of' F) = comulForestOfCuts admissibleCuts F :=
  comulOfCuts_apply_of' _ F

@[simp] theorem comulAlgHom_apply_ofTree (T : UnorderedTree α) :
    comulAlgHom (R := R) (α := α) (ofTree T) = comulTreeOfCuts admissibleCuts T :=
  comulOfCuts_apply_ofTree _ T

/-! ### Grafting `B⁺_a` -/

/-- `bPlus a` grafts a forest onto a new root labelled `a`, sending `of' F` to
`ofTree (node a F)`. -/
noncomputable def bPlus (a : α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  linearLift fun F ↦ ofTree (UnorderedTree.node a F)

@[simp] theorem bPlus_of' (a : α) (F : Forest (UnorderedTree α)) :
    bPlus (R := R) a (of' F) = ofTree (UnorderedTree.node a F) :=
  linearLift_of' _ F

@[simp] theorem bPlus_one (a : α) :
    bPlus (R := R) a (1 : ConnesKreimer R (UnorderedTree α)) = ofTree (UnorderedTree.leaf a) := by
  rw [← of'_zero, bPlus_of', UnorderedTree.node_zero]

/-! ### The cocycle -/

theorem comulTreeOfCuts_admissibleCuts_leaf (a : α) :
    comulTreeOfCuts (R := R) admissibleCuts (UnorderedTree.leaf a) =
      ofTree (UnorderedTree.leaf a) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree (UnorderedTree.leaf a) := by
  unfold comulTreeOfCuts
  rw [admissibleCuts_leaf, Multiset.map_singleton, Multiset.sum_singleton, of'_zero]

theorem comulTreeOfCuts_admissibleCuts_node (a : α) (F : Forest (UnorderedTree α)) :
    comulTreeOfCuts (R := R) admissibleCuts (UnorderedTree.node a F) =
      ofTree (UnorderedTree.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (LinearMap.lTensor _ (bPlus (R := R) a)) (comulForestOfCuts admissibleCuts F) := by
  unfold comulTreeOfCuts
  rw [admissibleCuts_node, comulForestOfCuts_eq_sum, map_multiset_sum, Multiset.map_map]
  simp [cutTensor]

/-- Grafting is a Hochschild 1-cocycle for Δ^ρ. -/
theorem comulAlgHom_bPlus_cocycle (a : α) (x : ConnesKreimer R (UnorderedTree α)) :
    comulAlgHom (bPlus (R := R) a x) =
      bPlus a x ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
        LinearMap.lTensor _ (bPlus a) (comulAlgHom x) := by
  have h : (comulAlgHom (R := R) (α := α)).toLinearMap ∘ₗ bPlus a =
      (TensorProduct.mk R _ _).flip 1 ∘ₗ bPlus a +
        LinearMap.lTensor _ (bPlus a) ∘ₗ (comulAlgHom (R := R) (α := α)).toLinearMap :=
    lhom_ext' fun F ↦ by simp [comulTreeOfCuts_admissibleCuts_node]
  exact congr($h x)

/-! ### Coassociativity

Both sides of coassociativity are algebra homomorphisms, so it is enough that they agree on every
tree. By induction they agree on the children of `node a F`, hence on the forest `F`, and the
cocycle carries the agreement from `F` to `B⁺_a F`. -/

private theorem coassoc_bPlus (a : α) {x : ConnesKreimer R (UnorderedTree α)}
    (hx : Algebra.TensorProduct.assoc R R R _ _ _
        (Algebra.TensorProduct.map comulAlgHom (AlgHom.id R _) (comulAlgHom x)) =
      Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHom (comulAlgHom x)) :
    Algebra.TensorProduct.assoc R R R _ _ _
        (Algebra.TensorProduct.map comulAlgHom (AlgHom.id R _)
          (comulAlgHom (bPlus (R := R) a x))) =
      Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHom (comulAlgHom (bPlus a x)) := by
  have h₁ (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
      Algebra.TensorProduct.map comulAlgHom (AlgHom.id R _) (LinearMap.lTensor _ (bPlus a) z) =
        LinearMap.lTensor _ (bPlus (R := R) a)
          (Algebra.TensorProduct.map comulAlgHom (AlgHom.id R _) z) := by
    induction z using TensorProduct.inductionOn <;> simp_all
  have h₂ (z : (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) ⊗[R]
      ConnesKreimer R (UnorderedTree α)) :
      Algebra.TensorProduct.assoc R R R _ _ _ (LinearMap.lTensor _ (bPlus a) z) =
        LinearMap.lTensor _ (LinearMap.lTensor _ (bPlus (R := R) a))
          (Algebra.TensorProduct.assoc R R R _ _ _ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul w c => induction w using TensorProduct.inductionOn <;> simp_all [TensorProduct.add_tmul]
    | _ => simp_all
  have h₃ (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
      Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHom (LinearMap.lTensor _ (bPlus a) z) =
        Algebra.TensorProduct.assoc R R R _ _ _ (LinearMap.lTensor _ (bPlus a) z ⊗ₜ 1) +
          LinearMap.lTensor _ (LinearMap.lTensor _ (bPlus (R := R) a))
            (Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHom z) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ ih₁ ih₂ => simp only [map_add, TensorProduct.add_tmul, ih₁, ih₂]; abel
    | _ => simp [comulAlgHom_bPlus_cocycle, TensorProduct.tmul_add]
  rw [comulAlgHom_bPlus_cocycle, map_add, map_add, map_add, h₁, h₂, hx, h₃,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgHom.id_apply, map_one, comulAlgHom_bPlus_cocycle, TensorProduct.add_tmul, map_add,
    Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.one_def]
  abel

theorem comulAlgHom_coassoc_algHom :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom (R := R) (α := α))
        (AlgHom.id R _)).comp comulAlgHom) =
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
      (comulAlgHom (R := R) (α := α))).comp comulAlgHom := by
  refine algHom_ext_ofTree fun T ↦ ?_
  induction T with
  | node a F ih =>
    rw [← bPlus_of']
    exact coassoc_bPlus a (algHom_of'_eq_of_ofTree ih)

/-- The Connes–Kreimer coproduct makes `ConnesKreimer R (UnorderedTree α)` a bialgebra over any
commutative semiring. -/
noncomputable instance instBialgebra :
    Bialgebra R (ConnesKreimer R (UnorderedTree α)) :=
  Bialgebra.ofAlgHom (A := ConnesKreimer R (UnorderedTree α)) comulAlgHom counit
    comulAlgHom_coassoc_algHom
    (rTensor_counit_comp_comulOfCuts admissibleCuts_filter_empty)
    (lTensor_counit_comp_comulOfCuts _)

instance instIsBialgebraCutsAdmissibleCuts : IsBialgebraCuts (admissibleCuts (α := α)) where
  coassoc _ _ := comulAlgHom_coassoc_algHom
  rTensor_counit_comp_comul _ _ := rTensor_counit_comp_comulOfCuts admissibleCuts_filter_empty

theorem coalgebra_comul_apply (x : ConnesKreimer R (UnorderedTree α)) :
    Coalgebra.comul (R := R) x = comulAlgHom x := rfl

theorem coalgebra_counit_apply (x : ConnesKreimer R (UnorderedTree α)) :
    CoalgebraStruct.counit (R := R) x = counit x := rfl

end ConnesKreimer
