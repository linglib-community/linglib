/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing
public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Linglib.Core.Data.Multiset.Antidiagonal
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Tactic.Ring

/-!
# The operator B⁻

This file defines the linear map `B⁻_a` on `ConnesKreimer R (UnorderedTree α)`. It sends a
one-tree forest whose root is labelled `a` to the forest of that root's children, and every other
basis forest to `0`, so it undoes the grafting operator `B⁺_a` of `Coproduct/Pruning.lean`. Oudom
and Guin use the pair `B⁺`, `B⁻` to identify the Grossman–Larson algebra with their product on a
symmetric algebra (their Proposition 4.1).

Under the symmetry-weighted pairing, `B⁻_a` is the transpose of `B⁺_a`, and it satisfies
`B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y` for the Grossman–Larson product. With the
multiplicativity of the counit (`GrossmanLarson.counit_product`), these drive the induction that
proves the duality of `Coproduct/PruningDuality.lean`.

## Main definitions

* `GrossmanLarson.bMinusLin`: the linear map `B⁻_a`; `bMinusTree` and `bMinusBasis` are its values
  on trees and on basis forests.

## Main results

* `GrossmanLarson.bMinusLin_pairing_adjoint`, `GrossmanLarson.isAdjointPair_bMinusLin_bPlusLin`:
  `⟨B⁻_a x, y⟩ = ⟨x, B⁺_a y⟩`.
* `GrossmanLarson.insertion_of'_singleton_node`: grafting into the tree `node a A` is
  `B⁺_a (A ⋆ B)`.
* `GrossmanLarson.bMinusLin_gl_mul`: `B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y`.
* `GrossmanLarson.pairing_apply_bPlus_gl_mul`: `⟨x ⋆ y, B⁺_a z⟩` in terms of `B⁻_a`.

## References

* [oudom-guin-2008]
* [foissy-2021]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### `B⁻_a` on trees and basis forests -/

/-- `bMinusTree a T` is the forest of children of `T` when its root is labelled `a`, else `0`. -/
noncomputable def bMinusTree (a : α) (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) :=
  if T.value = a then of' (R := R) T.children else 0

@[simp] theorem bMinusTree_node (a : α) (F : Forest (UnorderedTree α)) :
    bMinusTree (R := R) a (UnorderedTree.node a F) = of' F := by
  rw [bMinusTree, UnorderedTree.value_node, ite_eq_left rfl,
      UnorderedTree.children_node]

/-- `bMinusBasis a F` is `bMinusTree a T` when `F = {T}`, and `0` otherwise. It is stated through
`card`, `map` and `sum` so that it is a function on multisets. -/
noncomputable def bMinusBasis (a : α) (F : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) :=
  if F.card = 1 then (F.map (bMinusTree (R := R) a)).sum else 0

@[simp] theorem bMinusBasis_zero (a : α) :
    bMinusBasis (R := R) a (0 : Forest (UnorderedTree α)) = 0 := by
  simp [bMinusBasis]

@[simp] theorem bMinusBasis_singleton_node (a : α) (F : Forest (UnorderedTree α)) :
    bMinusBasis (R := R) a ({UnorderedTree.node a F} : Forest (UnorderedTree α)) =
      of' F := by
  simp [bMinusBasis]

theorem bMinusBasis_eq_zero_of_not_singleton_a (a : α)
    (F : Forest (UnorderedTree α))
    (h : ¬ ∃ G' : Forest (UnorderedTree α), F = ({UnorderedTree.node a G'} : Forest _)) :
    bMinusBasis (R := R) a F = 0 := by
  rw [bMinusBasis]
  split_ifs with hcard
  · obtain ⟨T, rfl⟩ := Multiset.card_eq_one.mp hcard
    rw [Multiset.map_singleton, Multiset.sum_singleton, bMinusTree, ite_eq_right]
    intro hlab
    exact h ⟨T.children, by rw [← hlab, UnorderedTree.node_eta]⟩
  · rfl

/-! ### The linear map -/

/-- `bMinusLin a` is the linear extension of `bMinusBasis a`. -/
noncomputable def bMinusLin (a : α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  ConnesKreimer.linearLift (bMinusBasis (R := R) a)

@[simp] theorem bMinusLin_of' (a : α) (F : Forest (UnorderedTree α)) :
    bMinusLin (R := R) a (of' F) = bMinusBasis (R := R) a F := by
  show ConnesKreimer.linearLift (bMinusBasis (R := R) a) (ConnesKreimer.of' F) = _
  rw [ConnesKreimer.linearLift_of']

/-! ### Transpose of `B⁺_a` -/

theorem bMinusLin_pairing_adjoint_basis (a : α)
    (F G : Forest (UnorderedTree α)) :
    pairing (R := R) (bMinusLin (R := R) a (of' F)) (of' G) =
    pairing (R := R) (of' F) (bPlusLin (R := R) a (of' G)) := by
  rw [bMinusLin_of',
      show bPlusLin (R := R) a (of' G) =
        of' ({UnorderedTree.node a G} : Forest (UnorderedTree α)) from
        ConnesKreimer.bPlusLin_of' a G,
      show pairing (R := R) (of' F)
          (of' ({UnorderedTree.node a G} : Forest (UnorderedTree α))) =
        (if F = ({UnorderedTree.node a G} : Forest (UnorderedTree α)) then
          (forestAutCard F : R) else 0) from pairing_of'_of' F _]
  by_cases hF : ∃ G' : Forest (UnorderedTree α), F = {UnorderedTree.node a G'}
  · obtain ⟨G', rfl⟩ := hF
    rw [bMinusBasis_singleton_node,
        show pairing (R := R) (of' G') (of' G) =
          (if G' = G then (forestAutCard G' : R) else 0) from
          pairing_of'_of' G' G]
    by_cases hG : G' = G
    · subst hG
      rw [ite_eq_left rfl, ite_eq_left rfl, UnorderedTree.forestAutCard_singleton,
          UnorderedTree.autCard_node]
    · rw [ite_eq_right hG, ite_eq_right fun h => hG (by
        simpa using congrArg UnorderedTree.children (Multiset.singleton_inj.mp h))]
  · rw [bMinusBasis_eq_zero_of_not_singleton_a a F hF,
        ite_eq_right fun h => hF ⟨G, h⟩, pairing_zero_left]

/-- `B⁻_a` and `B⁺_a` are an adjoint pair for the symmetry-weighted pairing. -/
theorem isAdjointPair_bMinusLin_bPlusLin (a : α) :
    LinearMap.IsAdjointPair (pairing (R := R)) (pairing (R := R))
      (bMinusLin (R := R) a) (ConnesKreimer.bPlusLin (R := R) a) := by
  rw [LinearMap.isAdjointPair_iff_comp_eq_compl₂]
  refine ConnesKreimer.lhom_ext' fun F => ?_
  refine ConnesKreimer.lhom_ext' fun G => ?_
  exact bMinusLin_pairing_adjoint_basis a F G

/-- `⟨B⁻_a x, y⟩ = ⟨x, B⁺_a y⟩`. -/
theorem bMinusLin_pairing_adjoint (a : α)
    (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (bMinusLin (R := R) a x) y =
    pairing (R := R) x (bPlusLin (R := R) a y) :=
  isAdjointPair_bMinusLin_bPlusLin a x y

/-! ### `B⁻_a` and the Grossman–Larson product

The identity `B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y` reduces to basis forests `x = of' A`.
If `A` is not a single tree with root `a`, both sides vanish or agree by counting trees. If
`A = {node a A'}`, grafting into `node a A'` is `B⁺_a` of the product `A' ⋆ B`
(`UnorderedTree.insertionMultiset_singleton_node`). -/

omit [DecidableEq α] in
/-- Grafting `of' B` into the single tree `node a A` is `B⁺_a` of the Grossman–Larson product
`of' A ⋆ of' B`: each guest is either a new child of the root or grafted into a tree of `A`. -/
theorem insertion_of'_singleton_node (a : α) (A B : Forest (UnorderedTree α)) :
    insertion (of' {UnorderedTree.node a A}) (of' B) =
      bPlusLin (R := R) a (product (of' A) (of' B)) := by
  rw [insertion_of'_of', insertionMultiset_singleton_node, product_of'_of',
    map_multiset_sum (bPlusLin (R := R) a), Multiset.map_map, Multiset.map_map]
  simp [bPlusLin_of']

private theorem bMinusBasis_singleton_node_add (a : α)
    (F G : Forest (UnorderedTree α)) :
    bMinusBasis (R := R) a ({UnorderedTree.node a F} + G) = if G = 0 then of' F else 0 := by
  split_ifs with hG
  · rw [hG, add_zero, bMinusBasis_singleton_node]
  · apply bMinusBasis_eq_zero_of_not_singleton_a
    rintro ⟨G', hG'⟩
    have hcard := congrArg Multiset.card hG'
    rw [Multiset.card_add, Multiset.card_singleton, Multiset.card_singleton] at hcard
    exact hG (Multiset.card_eq_zero.mp (by omega))

private theorem bMinusLin_bPlusLin_mul_of' (a : α)
    (Y : ConnesKreimer R (UnorderedTree α)) (G : Forest (UnorderedTree α)) :
    bMinusLin (R := R) a (bPlusLin (R := R) a Y * of' G) = if G = 0 then Y else 0 := by
  induction Y using ConnesKreimer.induction_linear with
  | zero => simp
  | add Y₁ Y₂ ih₁ ih₂ => rw [map_add, add_mul, map_add, ih₁, ih₂]; split_ifs <;> simp
  | single F r =>
    rw [← smul_of', map_smul, smul_mul_assoc, map_smul]
    change r • bMinusLin a (bPlusLin a (of' F) * of' G) = if G = 0 then r • of' F else 0
    rw [bPlusLin_of', ← of'_singleton, ← of'_add, bMinusLin_of', bMinusBasis_singleton_node_add]
    split_ifs <;> simp

private theorem sum_antidiagonal_ite_fst_eq_zero {β : Type*} [AddCommMonoid β]
    (B : Forest (UnorderedTree α)) (f : Forest (UnorderedTree α) → β) :
    (B.antidiagonal.map fun p ↦ if p.1 = 0 then f p.2 else 0).sum = f B := by
  induction B using Multiset.induction generalizing f with
  | empty => simp
  | cons T B ih =>
    rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map]
    simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Multiset.cons_ne_zero,
      ↓reduceIte, Multiset.map_const', Multiset.sum_replicate, smul_zero, add_zero]
    exact ih (f ∘ (T ::ₘ ·))

private theorem bMinusBasis_insertionMultiset_add_eq_zero (a : α)
    (A B₁ B' F' : Forest (UnorderedTree α))
    (hA_ne : A ≠ 0)
    (hA : ¬ ∃ G' : Forest (UnorderedTree α), A = ({UnorderedTree.node a G'} : Forest _))
    (hF' : F' ∈ UnorderedTree.insertionMultiset A B₁) :
    bMinusBasis (R := R) a (F' + B') = 0 := by
  apply bMinusBasis_eq_zero_of_not_singleton_a
  rintro ⟨G, hG⟩
  have hcard := congrArg Multiset.card hG
  rw [Multiset.card_add, UnorderedTree.insertionMultiset_card_eq A B₁ hF',
    Multiset.card_singleton] at hcard
  have hA_card : A.card = 1 := by
    have := Multiset.card_pos.mpr hA_ne
    omega
  obtain rfl : B' = 0 := Multiset.card_eq_zero.mp (by omega)
  obtain ⟨T, rfl⟩ := Multiset.card_eq_one.mp hA_card
  obtain ⟨T', rfl, hT'⟩ := UnorderedTree.insertionMultiset_singleton_value T B₁ hF'
  rw [add_zero, Multiset.singleton_inj] at hG
  subst hG
  rw [UnorderedTree.value_node] at hT'
  exact hA ⟨T.children, by rw [hT', UnorderedTree.node_eta]⟩

private theorem bMinusLin_gl_mul_basis (a : α) (A B : Forest (UnorderedTree α)) :
    bMinusLin (R := R) a (product (of' A) (of' B)) =
      counit (of' (R := R) A) • bMinusLin (R := R) a (of' B) +
        product (bMinusLin (R := R) a (of' A)) (of' B) := by
  by_cases hA : ∃ A' : Forest (UnorderedTree α), A = ({UnorderedTree.node a A'} : Forest _)
  · obtain ⟨A', rfl⟩ := hA
    simp only [counit_of', Multiset.card_singleton, one_ne_zero, ↓reduceIte, zero_smul, zero_add]
    rw [bMinusLin_of', bMinusBasis_singleton_node, product_of',
      map_multiset_sum (bMinusLin (R := R) a), Multiset.map_map]
    simp only [Function.comp_def, insertion_of'_singleton_node, bMinusLin_bPlusLin_mul_of']
    exact sum_antidiagonal_ite_fst_eq_zero B fun G ↦ product (of' A') (of' G)
  · rw [bMinusLin_of' a A, bMinusBasis_eq_zero_of_not_singleton_a a A hA, map_zero,
      LinearMap.zero_apply, add_zero]
    rcases eq_or_ne A 0 with rfl | hA0
    · rw [of'_zero, product_one_left, counit_one, one_smul]
    · simp only [counit_of', Multiset.card_eq_zero, hA0, ↓reduceIte, zero_smul]
      rw [product_of'_of', map_multiset_sum (bMinusLin (R := R) a), Multiset.map_map]
      refine Multiset.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨p, -, hW⟩ := Multiset.mem_bind.mp hW
      obtain ⟨X, hX, rfl⟩ := Multiset.mem_map.mp hW
      rw [Function.comp_apply, bMinusLin_of']
      exact bMinusBasis_insertionMultiset_add_eq_zero a A p.2 p.1 X hA0 hA hX

/-- `B⁻_a (x ⋆ y) = ε(x) • B⁻_a y + B⁻_a x ⋆ y`. -/
theorem bMinusLin_gl_mul (a : α) (x y : ConnesKreimer R (UnorderedTree α)) :
    bMinusLin (R := R) a (product x y) =
      counit x • bMinusLin (R := R) a y + product (bMinusLin (R := R) a x) y := by
  have h : product.compr₂ (bMinusLin (R := R) a) =
      (counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R).toLinearMap.smulRight
          (bMinusLin (R := R) a) + product.comp (bMinusLin (R := R) a) :=
    lhom_ext' fun A ↦ lhom_ext' fun B ↦ bMinusLin_gl_mul_basis a A B
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- `⟨X ⋆ Y, B⁺_a z⟩ = ε(X) · ⟨B⁻_a Y, z⟩ + ⟨B⁻_a X ⋆ Y, z⟩`. -/
theorem pairing_apply_bPlus_gl_mul (a : α)
    (X Y z : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (product X Y) (bPlusLin (R := R) a z) =
      counit X * pairing (R := R) (bMinusLin (R := R) a Y) z +
        pairing (R := R) (product (bMinusLin (R := R) a X) Y) z := by
  rw [← bMinusLin_pairing_adjoint, bMinusLin_gl_mul, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]

end GrossmanLarson
