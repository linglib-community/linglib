/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing
public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The operator B⁻

This file defines the linear map `B⁻_a` on `ConnesKreimer R (UnorderedTree α)`, which removes a
root labelled `a`: it sends the one-tree forest `{node a F}` to `F` and every other forest to `0`.
It is a left inverse of the grafting operator `B⁺_a` of `Coproduct/Pruning.lean`, and the
transpose of `B⁺_a` under the symmetry-weighted pairing.

Oudom and Guin identify the Grossman–Larson algebra with their product on the symmetric algebra
through `B⁺` and `B⁻` (their Proposition 4.1), by `B⁺_a(x) ∘ y = B⁺_a(x ⋆ y)`. It follows that
`B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y`. Under the pairing these are the facts about
`⟨F ⋆ G, T⟩` in Foissy's proof of his Proposition 5.2, the one-tree step of the duality in
`Coproduct/PruningDuality.lean`.

## Main definitions

* `ConnesKreimer.bMinus`: the linear map `B⁻_a`.

## Main results

* `ConnesKreimer.coeff_bMinus`: the coefficient of `B⁻_a x` at `F` is that of `x` at
  `{node a F}`.
* `GrossmanLarson.insertion_bPlus`: `B⁺_a(x) ∘ y = B⁺_a(x ⋆ y)`.
* `GrossmanLarson.bMinus_product`: `B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y`.
* `GrossmanLarson.isAdjointPair_bMinus_bPlus`: `⟨B⁻_a x, y⟩ = ⟨x, B⁺_a y⟩`.

## Implementation notes

`B⁻_a` pulls the coefficients back along the injection `F ↦ {node a F}`, as
`AddMonoidAlgebra.divOf` pulls them back along `d ↦ g + d`. Oudom and Guin define `B⁻` on trees
only, as the inverse of `B⁺`; sending the other forests to `0` makes it the transpose of `B⁺`.

## Errata

* In the proof of Foissy's Proposition 5.2, `⟨1 ⋆ T, T⟩` is printed as `1`. Since `1 ⋆ T = T`,
  it is the number of symmetries of `T`, which is `2` for a root with two identical leaves.

## References

* [oudom-guin-2008]
* [foissy-2021]
-/

@[expose] public section

open UnorderedTree

namespace ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- `bMinus a x` moves the coefficient of each one-tree forest `{node a F}` of `x` to `F` and
drops the rest. -/
noncomputable def bMinus (a : α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) where
  toFun x := ⟨x.toFinsupp.comapDomain (fun F ↦ {node a F})
    fun _ _ h ↦ node_injective a (Multiset.singleton_inj.mp h)⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

@[simp] theorem coeff_bMinus (a : α) (x : ConnesKreimer R (UnorderedTree α))
    (F : Forest (UnorderedTree α)) : (bMinus a x).coeff F = x.coeff {node a F} :=
  rfl

theorem bMinus_of'_of_forall_ne (a : α) {F : Forest (UnorderedTree α)}
    (h : ∀ G, {node a G} ≠ F) : bMinus (R := R) a (of' F) = 0 := by
  classical
  exact ext_coeff fun G ↦ by simp [coeff_of', (h G).symm]

@[simp] theorem bMinus_ofTree_node (a : α) (F : Forest (UnorderedTree α)) :
    bMinus (R := R) a (ofTree (node a F)) = of' F := by
  classical
  exact ext_coeff fun G ↦ by simp [← of'_singleton, coeff_of']

theorem bMinus_of'_of_card_ne_one (a : α) {F : Forest (UnorderedTree α)} (h : F.card ≠ 1) :
    bMinus (R := R) a (of' F) = 0 :=
  bMinus_of'_of_forall_ne a fun _ hG ↦ h (hG ▸ Multiset.card_singleton _)

@[simp] theorem bMinus_one (a : α) :
    bMinus (R := R) a (1 : ConnesKreimer R (UnorderedTree α)) = 0 := by
  rw [← of'_zero, bMinus_of'_of_card_ne_one a (by simp)]

@[simp] theorem bMinus_bPlus (a : α) (x : ConnesKreimer R (UnorderedTree α)) :
    bMinus a (bPlus a x) = x :=
  LinearMap.congr_fun (lhom_ext' (f := bMinus a ∘ₗ bPlus a) (g := .id) fun F ↦ by simp) x

/-- `B⁻_a` is a derivation of the disjoint union along the counit, since a one-tree forest is a
disjoint union only with the empty forest. -/
theorem bMinus_mul (a : α) (x y : ConnesKreimer R (UnorderedTree α)) :
    bMinus a (x * y) = counit x • bMinus a y + counit y • bMinus a x := by
  let S := (counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R).toLinearMap.smulRight
    (bMinus (R := R) a)
  have h : (LinearMap.mul R (ConnesKreimer R (UnorderedTree α))).compr₂ (bMinus a) =
      S + S.flip := lhom_ext' fun A ↦ lhom_ext' fun B ↦ by
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
      LinearMap.flip_apply, S, LinearMap.smulRight_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply, ← of'_add]
    rcases eq_or_ne A 0 with rfl | hA
    · simp
    rcases eq_or_ne B 0 with rfl | hB
    · simp
    have := Multiset.card_pos.mpr hA
    have := Multiset.card_pos.mpr hB
    rw [bMinus_of'_of_card_ne_one a (by rw [Multiset.card_add]; omega)]
    simp [counit_of', hA, hB]
  exact LinearMap.congr_fun₂ h x y

end ConnesKreimer

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- Grafting onto `B⁺_a x` puts each guest on the new root or into `x`:
`B⁺_a(x) ∘ y = B⁺_a(x ⋆ y)`. This is the computation in Oudom and Guin's proof of their
Proposition 4.1. -/
theorem insertion_bPlus (a : α) (x y : ConnesKreimer R (UnorderedTree α)) :
    insertion (bPlus a x) y = bPlus a (product x y) := by
  have h : insertion.comp (bPlus (R := R) a) = product.compr₂ (bPlus a) :=
    lhom_ext' fun A ↦ lhom_ext' fun B ↦ by
      rw [LinearMap.comp_apply, LinearMap.compr₂_apply, bPlus_of', ← of'_singleton,
        insertion_of'_of', insertionMultiset_singleton_node, product_of'_of',
        map_multiset_sum, Multiset.map_map, Multiset.map_map]
      simp [bPlus_of']
  exact LinearMap.congr_fun₂ h x y

theorem bMinus_insertion (a : α) (x y : ConnesKreimer R (UnorderedTree α)) :
    bMinus a (insertion x y) = product (bMinus a x) y := by
  have h : insertion.compr₂ (bMinus (R := R) a) = product.comp (bMinus a) :=
    lhom_ext' fun A ↦ lhom_ext' fun B ↦ by
      rw [LinearMap.compr₂_apply, LinearMap.comp_apply]
      by_cases hA : ∃ F, A = {node a F}
      · obtain ⟨F, rfl⟩ := hA
        rw [of'_singleton, ← bPlus_of', insertion_bPlus, bMinus_bPlus, bMinus_bPlus]
      rw [bMinus_of'_of_forall_ne a fun F h ↦ hA ⟨F, h.symm⟩, map_zero, LinearMap.zero_apply,
        insertion_of'_of', map_multiset_sum, Multiset.map_map]
      refine Multiset.sum_eq_zero fun _ hz ↦ ?_
      obtain ⟨X, hX, rfl⟩ := Multiset.mem_map.mp hz
      exact bMinus_of'_of_forall_ne a fun G hG ↦
        hA (exists_eq_singleton_node_of_mem_insertionMultiset (hG ▸ hX))
  exact LinearMap.congr_fun₂ h x y

/-- `B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y`, from `x ⋆ G = Σ (x ∘ G₂) G₁` by `bMinus_mul`
and `bMinus_insertion`. -/
theorem bMinus_product (a : α) (x y : ConnesKreimer R (UnorderedTree α)) :
    bMinus a (product x y) = counit x • bMinus a y + product (bMinus a x) y := by
  -- `1 ⋆ G = G`, read through `product_of'`.
  have hε (G : Forest (UnorderedTree α)) :
      (G.antidiagonal.map fun p ↦ counit (of' (R := R) p.2) • of' (R := R) p.1).sum = of' G := by
    simpa [product_of', insertion_one_left] using product_one_left (of' (R := R) G)
  refine LinearMap.congr_fun (lhom_ext' (f := bMinus a ∘ₗ product x)
    (g := counit x • bMinus a + product (bMinus a x)) fun G ↦ ?_) y
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [product_of', map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def, bMinus_mul, counit_insertion, bMinus_insertion,
    Multiset.sum_map_add]
  congr 1
  · rw [← hε G, map_multiset_sum, Multiset.smul_sum, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, map_smul, smul_smul]
  · rw [← Multiset.map_swap_antidiagonal, Multiset.map_map]
    conv_rhs => rw [← hε G, map_multiset_sum, Multiset.map_map]
    simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, map_smul]

/-! ### Transpose of `B⁺_a` -/

variable [DecidableEq α]

theorem pairing_bMinus (a : α) (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (bMinus a x) y = pairing x (bPlus a y) := by
  refine LinearMap.congr_fun (lhom_ext' (f := pairing (bMinus a x)) (g := pairing x ∘ₗ bPlus a)
    fun G ↦ ?_) y
  rw [LinearMap.comp_apply, bPlus_of', ← of'_singleton, pairing_apply_of', pairing_apply_of',
    coeff_bMinus, forestAutCard_singleton, autCard_node]

/-- `B⁻_a` and `B⁺_a` are an adjoint pair for the symmetry-weighted pairing. -/
theorem isAdjointPair_bMinus_bPlus (a : α) :
    LinearMap.IsAdjointPair (pairing (R := R)) pairing (bMinus a) (bPlus a) :=
  pairing_bMinus a

theorem pairing_product_bPlus (a : α) (x y z : ConnesKreimer R (UnorderedTree α)) :
    pairing (product x y) (bPlus a z) =
      counit x * pairing (bMinus a y) z + pairing (product (bMinus a x) y) z := by
  rw [← pairing_bMinus, bMinus_product, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]

end GrossmanLarson
