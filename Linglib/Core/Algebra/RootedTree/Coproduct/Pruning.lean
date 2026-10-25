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
# The pruning coproduct Δ^ρ

The Connes–Kreimer coproduct on unordered rooted trees, summing over admissible cuts that prune
the cut subtrees. Grafting `B⁺_a` is a Hochschild 1-cocycle for it, and the counit laws and
coassociativity follow from the cocycle by induction on trees.

## Main definitions

* `ConnesKreimer.comulTreeN`, `ConnesKreimer.comulForestN`, `ConnesKreimer.comulAlgHomN`: the
  Δ^ρ coproduct, as the generic admissible-cut coproduct (`Coproduct/WithCuts.lean`) at the
  enumeration `cutSummandsN`.
* `ConnesKreimer.bPlus`: grafting `B⁺_a` as a linear map.

## Main results

* `ConnesKreimer.comulAlgHomN_bPlus_cocycle`: the Hochschild 1-cocycle law
  `Δ^ρ (B⁺_a x) = B⁺_a x ⊗ 1 + (id ⊗ B⁺_a) (Δ^ρ x)`.
* `ConnesKreimer.counit_rTensor_comulAlgHomN`, `ConnesKreimer.counit_lTensor_comulAlgHomN`: the
  counit laws.
* `ConnesKreimer.comulAlgHomN_coassoc_algHom`: coassociativity.
* `ConnesKreimer.instBialgebraRho`: the Δ^ρ `Bialgebra`, over any `CommSemiring`; the pruning
  cuts are admissible (`ConnesKreimer.instIsAdmissibleCutsN`).

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

/-- The pruning coproduct Δ^ρ of a tree, which is `comulTreeNG` at the pruning cuts. -/
noncomputable def comulTreeN :
    UnorderedTree α →
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulTreeNG cutSummandsN

/-- The nonplanar forest-level Δ^ρ (multiplicative extension). -/
noncomputable def comulForestN :
    Forest (UnorderedTree α) →
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulForestNG cutSummandsN

@[simp] theorem comulForestN_zero :
    comulForestN (R := R) (0 : Forest (UnorderedTree α)) = 1 :=
  comulForestNG_zero _

@[simp] theorem comulForestN_add (F G : Forest (UnorderedTree α)) :
    comulForestN (R := R) (F + G) =
      comulForestN (R := R) F * comulForestN (R := R) G :=
  comulForestNG_add _ F G

@[simp] theorem comulForestN_cons (T : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    comulForestN (R := R) (T ::ₘ F) =
      comulTreeN (R := R) T * comulForestN (R := R) F :=
  comulForestNG_cons _ T F

/-- The pruning coproduct Δ^ρ as an algebra homomorphism, which is `comulAlgHomNG` at the
pruning cuts. -/
noncomputable def comulAlgHomN :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulAlgHomNG cutSummandsN

@[simp] theorem comulAlgHomN_apply_of' (F : Forest (UnorderedTree α)) :
    comulAlgHomN (R := R) (α := α) (of' F) = comulForestN F :=
  comulAlgHomNG_apply_of' _ F

@[simp] theorem comulAlgHomN_apply_ofTree (T : UnorderedTree α) :
    comulAlgHomN (R := R) (α := α) (ofTree T) = comulTreeN T :=
  comulAlgHomNG_apply_ofTree _ T

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

theorem comulTreeN_leaf (a : α) :
    comulTreeN (R := R) (UnorderedTree.leaf a) =
      ofTree (UnorderedTree.leaf a) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree (UnorderedTree.leaf a) := by
  unfold comulTreeN comulTreeNG
  rw [cutSummandsN_leaf, Multiset.map_singleton, Multiset.sum_singleton, of'_zero]

theorem comulTreeN_node_cocycle (a : α) (F : Forest (UnorderedTree α)) :
    comulTreeN (R := R) (UnorderedTree.node a F) =
      ofTree (UnorderedTree.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (LinearMap.lTensor _ (bPlus (R := R) a)) (comulForestN F) := by
  unfold comulTreeN comulTreeNG comulForestN
  rw [cutSummandsN_node, comulForestNG_eq_sum, map_multiset_sum, Multiset.map_map]
  simp [cutTensor]

/-- Grafting is a Hochschild 1-cocycle for Δ^ρ. -/
theorem comulAlgHomN_bPlus_cocycle (a : α) (x : ConnesKreimer R (UnorderedTree α)) :
    comulAlgHomN (bPlus (R := R) a x) =
      bPlus a x ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
        LinearMap.lTensor _ (bPlus a) (comulAlgHomN x) := by
  have h : (comulAlgHomN (R := R) (α := α)).toLinearMap ∘ₗ bPlus a =
      (TensorProduct.mk R _ _).flip 1 ∘ₗ bPlus a +
        LinearMap.lTensor _ (bPlus a) ∘ₗ (comulAlgHomN (R := R) (α := α)).toLinearMap :=
    lhom_ext' fun F ↦ by simp [comulTreeN_node_cocycle]
  exact congr($h x)

/-! ### Counit laws

`(ε ⊗ id) ∘ Δ^ρ = lid⁻¹` and `(id ⊗ ε) ∘ Δ^ρ = rid⁻¹`, checked on trees through the cocycle
`comulTreeN_node_cocycle`. The left law needs induction on the tree. -/

private theorem counit_bPlus (a : α) (y : ConnesKreimer R (UnorderedTree α)) :
    counit (R := R) (bPlus (R := R) a y) = 0 := by
  have h : (counit (R := R)).toLinearMap ∘ₗ bPlus (R := R) a = 0 :=
    lhom_ext' fun F ↦ by simp
  exact congr($h y)

theorem counit_rTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (counit (R := R)) (AlgHom.id R _)).comp comulAlgHomN =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (UnorderedTree α))).symm.toAlgHom := by
  refine algHom_ext_ofTree fun T ↦ ?_
  induction T with
  | node a F ih =>
    have hF := algHom_of'_eq_of_ofTree ih
    have h (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
        Algebra.TensorProduct.map counit (AlgHom.id R _)
          (LinearMap.lTensor _ (bPlus (R := R) a) z) =
        LinearMap.lTensor R (bPlus a) (Algebra.TensorProduct.map counit (AlgHom.id R _) z) := by
      induction z using TensorProduct.inductionOn <;> simp_all
    simp [comulTreeN_node_cocycle, h, by simpa using hF]

theorem counit_lTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (AlgHom.id R _) (counit (R := R))).comp comulAlgHomN =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (UnorderedTree α))).symm.toAlgHom := by
  refine algHom_ext_ofTree fun T ↦ ?_
  obtain ⟨a, F, rfl⟩ : ∃ a F, T = UnorderedTree.node a F := ⟨_, _, (node_eta T).symm⟩
  have h (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
      Algebra.TensorProduct.map (AlgHom.id R _) counit
        (LinearMap.lTensor _ (bPlus (R := R) a) z) = 0 := by
    induction z using TensorProduct.inductionOn <;> simp_all [counit_bPlus]
  simp [comulTreeN_node_cocycle, h]

/-! ### Coassociativity

Both sides of coassociativity are algebra homomorphisms, so it is enough that they agree on every
tree. By induction they agree on the children of `node a F`, hence on the forest `F`, and the
cocycle carries the agreement from `F` to `B⁺_a F`. -/

private theorem coassoc_bPlus (a : α) {x : ConnesKreimer R (UnorderedTree α)}
    (hx : Algebra.TensorProduct.assoc R R R _ _ _
        (Algebra.TensorProduct.map comulAlgHomN (AlgHom.id R _) (comulAlgHomN x)) =
      Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHomN (comulAlgHomN x)) :
    Algebra.TensorProduct.assoc R R R _ _ _
        (Algebra.TensorProduct.map comulAlgHomN (AlgHom.id R _)
          (comulAlgHomN (bPlus (R := R) a x))) =
      Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHomN (comulAlgHomN (bPlus a x)) := by
  have h₁ (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
      Algebra.TensorProduct.map comulAlgHomN (AlgHom.id R _) (LinearMap.lTensor _ (bPlus a) z) =
        LinearMap.lTensor _ (bPlus (R := R) a)
          (Algebra.TensorProduct.map comulAlgHomN (AlgHom.id R _) z) := by
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
      Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHomN (LinearMap.lTensor _ (bPlus a) z) =
        Algebra.TensorProduct.assoc R R R _ _ _ (LinearMap.lTensor _ (bPlus a) z ⊗ₜ 1) +
          LinearMap.lTensor _ (LinearMap.lTensor _ (bPlus (R := R) a))
            (Algebra.TensorProduct.map (AlgHom.id R _) comulAlgHomN z) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ ih₁ ih₂ => simp only [map_add, TensorProduct.add_tmul, ih₁, ih₂]; abel
    | _ => simp [comulAlgHomN_bPlus_cocycle, TensorProduct.tmul_add]
  rw [comulAlgHomN_bPlus_cocycle, map_add, map_add, map_add, h₁, h₂, hx, h₃,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgHom.id_apply, map_one, comulAlgHomN_bPlus_cocycle, TensorProduct.add_tmul, map_add,
    Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.one_def]
  abel

theorem comulAlgHomN_coassoc_algHom :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R _)).comp comulAlgHomN) =
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
      (comulAlgHomN (R := R) (α := α))).comp comulAlgHomN := by
  refine algHom_ext_ofTree fun T ↦ ?_
  induction T with
  | node a F ih =>
    rw [← bPlus_of']
    exact coassoc_bPlus a (algHom_of'_eq_of_ofTree ih)

/-- The pruning coproduct makes `ConnesKreimer R (UnorderedTree α)` a bialgebra over any
commutative semiring. -/
noncomputable instance instBialgebraRho :
    Bialgebra R (ConnesKreimer R (UnorderedTree α)) :=
  Bialgebra.ofAlgHom (A := ConnesKreimer R (UnorderedTree α)) comulAlgHomN counit
    comulAlgHomN_coassoc_algHom
    counit_rTensor_comulAlgHomN
    counit_lTensor_comulAlgHomN

instance instIsAdmissibleCutsN : IsAdmissibleCuts (cutSummandsN (α := α)) where
  coassoc _ _ := comulAlgHomN_coassoc_algHom
  counit_rTensor _ _ := counit_rTensor_comulAlgHomN
  counit_lTensor _ _ := counit_lTensor_comulAlgHomN

theorem coalgebra_comul_apply (x : ConnesKreimer R (UnorderedTree α)) :
    Coalgebra.comul (R := R) x = comulAlgHomN x := rfl

theorem coalgebra_counit_apply (x : ConnesKreimer R (UnorderedTree α)) :
    CoalgebraStruct.counit (R := R) x = counit x := rfl

end ConnesKreimer
