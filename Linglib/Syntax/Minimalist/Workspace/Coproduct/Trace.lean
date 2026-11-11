/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.DoubleCut
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# The coproduct with trace markers

This file defines the coproduct `Δ^c` of Marcolli, Chomsky and Berwick on forests of trees whose
vertices are labelled `α ⊕ β`. It sums over the admissible cuts of a tree, pairing the cut-off
subtrees with the remaining trunk, in which each cut subtree `S` leaves a trace leaf `inr (τ S)`
computed by a trace encoder `τ`. With the edge grading of `TraceGrading.lean` this gives
their Lemma 1.2.10: disjoint union and `Δ^c` make a graded bialgebra.

## Main definitions

* `ConnesKreimer.traceComulAlgHom`: `Δ^c` as an algebra homomorphism, for a trace encoder `τ`.
* `ConnesKreimer.TraceCoherent`: `τ` gives a cut trunk the same marker as the tree it was cut
  from.

## Main results

* `ConnesKreimer.traceComul_coassoc`: `Δ^c` is coassociative for a coherent encoder.
* `ConnesKreimer.instIsBialgebraCutsTraceCuts`: the counit laws and coassociativity, which give
  `WithCuts R (traceCuts τ)` its `Bialgebra` instance.

## Implementation notes

Coassociativity is proved directly: both composites enumerate pairs of nested admissible cuts,
and the two enumerations agree under trace coherence (`doubleCuts_eq`). The pairing duality
that gives coassociativity of the Connes–Kreimer coproduct in `Coproduct/AdmissibleCutDuality.lean`
fails here, because grafting never removes trace markers.

## References

* [marcolli-chomsky-berwick-2025]
* [foissy-2021]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### `Δ^c` on trees and forests

These instantiate the admissible-cut coproduct of `Coproduct/WithCuts.lean` at the enumeration
`traceCuts τ`. -/

/-- `traceComulAlgHom τ` is the coproduct `Δ^c` on `ConnesKreimer R (UnorderedTree (α ⊕ β))`, an
algebra homomorphism, for the trace encoder `τ`. -/
noncomputable def traceComulAlgHom (τ : UnorderedTree (α ⊕ β) → β) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  comulOfCuts (traceCuts τ)

@[simp] theorem traceComulAlgHom_apply_of' (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (UnorderedTree (α ⊕ β))) :
    traceComulAlgHom (R := R) τ (ConnesKreimer.of' F) = comulForestOfCuts (traceCuts τ) F :=
  comulOfCuts_apply_of' _ F

@[simp] theorem traceComulAlgHom_apply_ofTree (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    traceComulAlgHom (R := R) τ (ConnesKreimer.ofTree T) = comulTreeOfCuts (traceCuts τ) T :=
  comulOfCuts_apply_ofTree _ T

/-! ### Trace coherence

Coassociativity of `Δ^c` depends on the trace encoder. Iterating `Δ^c` encodes a subtree that
already carries markers, while the other cut order encodes the original subtree; for `τ` the
number of `inl` vertices the two disagree on a three-vertex chain of `inl` vertices. Marcolli,
Chomsky and Berwick's proof of Lemma 1.2.10 (pp. 37–38) uses that "the accessible terms of
accessible terms … are themselves accessible terms", and `TraceCoherent` states the hypothesis
this needs. -/

/-- A trace encoder `τ` is coherent when it gives a cut trunk, with its trace markers, the same
marker as the tree it was cut from. Constant encoders are coherent (`traceCoherent_const`). -/
def TraceCoherent (τ : UnorderedTree (α ⊕ β) → β) : Prop :=
  ∀ T : UnorderedTree (α ⊕ β), ∀ p ∈ traceCuts τ T, τ p.2 = τ T

/-- Constant trace encoders are coherent. -/
theorem traceCoherent_const (b : β) :
    TraceCoherent (fun _ : UnorderedTree (α ⊕ β) => b) :=
  fun _ _ _ => rfl

/-! ### Enumerating pairs of nested cuts

Both `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` sum over pairs of nested admissible cuts of a tree:
each composite is a sum over a double-cut enumeration (`doubleCutsCrown`, `doubleCutsTrunk`) at the
trace cuts. -/

section DoubleCut
variable {R : Type*} [CommSemiring R] {α β : Type*}

/-- Triple-tensor factor for the coassoc target `CK ⊗ (CK ⊗ CK)`. -/
private noncomputable def tripleTensor
    (q : Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β)) ×
         Forest (UnorderedTree (α ⊕ β))) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
      (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β))) :=
  ConnesKreimer.of' (R := R) q.1 ⊗ₜ[R]
    (ConnesKreimer.of' q.2.1 ⊗ₜ[R] ConnesKreimer.of' q.2.2)

/-- Cutting the crown of one cut pair again enumerates the crown's forest cuts. -/
private theorem lhs_per_pair (τ : UnorderedTree (α ⊕ β) → β)
    (A B : Forest (UnorderedTree (α ⊕ β))) :
    (TensorProduct.assoc R (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β))) (ConnesKreimer R (UnorderedTree (α ⊕ β))))
        (comulForestOfCuts (R := R) (traceCuts τ) A ⊗ₜ[R] ConnesKreimer.of' B) =
      ((forestCuts (traceCuts τ) A).map
        (fun A12 => tripleTensor (R := R) (A12.1, A12.2, B))).sum := by
  rw [comulForestOfCuts_eq_sum]
  let φ : (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
                ConnesKreimer R (UnorderedTree (α ⊕ β))) :=
    (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
      ((TensorProduct.mk R _ _).flip (ConnesKreimer.of' B))
  show φ ((Multiset.map (cutTensor (R := R)) (forestCuts (traceCuts τ) A)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  show (TensorProduct.assoc R _ _ _)
      ((ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.of' p.2) ⊗ₜ[R]
        ConnesKreimer.of' B) = _
  rw [TensorProduct.assoc_tmul]
  rfl

/-- Cutting the trunk of one cut pair again enumerates the trunk's forest cuts. -/
private theorem rhs_per_pair (τ : UnorderedTree (α ⊕ β) → β)
    (A B : Forest (UnorderedTree (α ⊕ β))) :
    ConnesKreimer.of' (R := R) A ⊗ₜ[R] comulForestOfCuts (R := R) (traceCuts τ) B =
      ((forestCuts (traceCuts τ) B).map
        (fun B12 => tripleTensor (R := R) (A, B12.1, B12.2))).sum := by
  rw [comulForestOfCuts_eq_sum]
  let ψ : (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
                ConnesKreimer R (UnorderedTree (α ⊕ β))) :=
    (TensorProduct.mk R _ _) (ConnesKreimer.of' A)
  show ψ ((Multiset.map (cutTensor (R := R)) (forestCuts (traceCuts τ) B)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  rfl

/-- The composite `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c` on a tree sums the `doubleCutsCrown`
    enumeration. -/
private theorem lhsExpand (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    (TensorProduct.assoc R (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β))) (ConnesKreimer R (UnorderedTree (α ⊕ β))))
        ((traceComulAlgHom (R := R) τ).toLinearMap.rTensor _ (comulTreeOfCuts (traceCuts τ) T)) =
      ((doubleCutsCrown (traceCuts τ) T).map (tripleTensor (R := R))).sum := by
  rw [comulTreeOfCuts_eq_sum]
  let Λ := (TensorProduct.assoc R (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β)))).toLinearMap ∘ₗ
      (traceComulAlgHom (R := R) τ).toLinearMap.rTensor
        (ConnesKreimer R (UnorderedTree (α ⊕ β)))
  show Λ ((Multiset.map (cutTensor (R := R)) (treeCuts (traceCuts τ) T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold doubleCutsCrown
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show Λ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCuts (traceCuts τ) A).map (fun A12 => (A12.1, A12.2, B)))).sum
  rw [Multiset.map_map]
  show (TensorProduct.assoc R _ _ _)
      ((traceComulAlgHom (R := R) τ).toLinearMap.rTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B)) = _
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, traceComulAlgHom_apply_of',
      lhs_per_pair]
  rfl

/-- The composite `(id ⊗ Δ^c) ∘ Δ^c` on a tree sums the `doubleCutsTrunk` enumeration. -/
private theorem rhsExpand (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    (traceComulAlgHom (R := R) τ).toLinearMap.lTensor _ (comulTreeOfCuts (traceCuts τ) T) =
      ((doubleCutsTrunk (traceCuts τ) T).map (tripleTensor (R := R))).sum := by
  rw [comulTreeOfCuts_eq_sum]
  show (traceComulAlgHom (R := R) τ).toLinearMap.lTensor _
        ((Multiset.map (cutTensor (R := R)) (treeCuts (traceCuts τ) T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold doubleCutsTrunk
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show (traceComulAlgHom (R := R) τ).toLinearMap.lTensor _ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCuts (traceCuts τ) B).map (fun B12 => (A, B12.1, B12.2)))).sum
  rw [Multiset.map_map]
  show (traceComulAlgHom (R := R) τ).toLinearMap.lTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B) = _
  rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, traceComulAlgHom_apply_of',
      rhs_per_pair]
  rfl

/-! ### Descent of the double-cut enumerations

The enumerations at the trace cuts are the images under `UnorderedTree.mk` of the enumerations on
rose trees, which `doubleCuts_eq` identifies. -/

/-- Under trace coherence the two double-cut enumerations of a tree agree, the combinatorial core
of Marcolli, Chomsky and Berwick's Lemma 1.2.10. -/
private theorem doubleCutsCrown_eq_doubleCutsTrunk (τ : UnorderedTree (α ⊕ β) → β)
    (hτ : TraceCoherent τ) (T : UnorderedTree (α ⊕ β)) :
    doubleCutsCrown (traceCuts τ) T = doubleCutsTrunk (traceCuts τ) T :=
  Quotient.inductionOn T fun t ↦ by
    have h (t : RoseTree (α ⊕ β)) : traceCuts τ (UnorderedTree.mk t) =
        (rootCuts (leaveTrace (τ ∘ UnorderedTree.mk)) t).map
          (Prod.map (Multiset.map UnorderedTree.mk) UnorderedTree.mk) := rfl
    have hcoh (t : RoseTree (α ⊕ β)) (p) (hp : p ∈ rootCuts (leaveTrace (τ ∘ UnorderedTree.mk)) t) :
        (τ ∘ UnorderedTree.mk) p.2 = (τ ∘ UnorderedTree.mk) t :=
      hτ (UnorderedTree.mk t) (projCut p) (Multiset.mem_map.mpr ⟨p, hp, rfl⟩)
    exact (doubleCutsCrown_map h t).trans <| (doubleCuts_eq _ hcoh t).trans
      (doubleCutsTrunk_map h t).symm

end DoubleCut

/-! ### Coassociativity

The statements are over a commutative ring for the `Bialgebra` consumers; the proof itself works
over a commutative semiring. -/

section CoassocCommRing
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- On a tree, both composites enumerate the pairs of nested admissible cuts of `T`, and
`TraceCoherent τ` makes the markers written by the two cut orders agree. -/
theorem traceComul_coassoc_tree
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ)
    (T : UnorderedTree (α' ⊕ β')) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        ((traceComulAlgHom (R := R') τ).toLinearMap.rTensor _ (comulTreeOfCuts (traceCuts τ) T)) =
      (traceComulAlgHom (R := R') τ).toLinearMap.lTensor _ (comulTreeOfCuts (traceCuts τ) T) := by
  rw [lhsExpand, rhsExpand, doubleCutsCrown_eq_doubleCutsTrunk τ hτ T]

/-- `coassocLHSAlgC τ` is `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c`. -/
private noncomputable def coassocLHSAlgC (τ : UnorderedTree (α' ⊕ β') → β') :
    ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R']
      ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
          ConnesKreimer R' (UnorderedTree (α' ⊕ β'))) :=
  (Algebra.TensorProduct.assoc R' R' R' _ _ _).toAlgHom.comp
    ((Algebra.TensorProduct.map (traceComulAlgHom (R := R') τ)
      (AlgHom.id R' _)).comp (traceComulAlgHom τ))

/-- `coassocRHSAlgC τ` is `(id ⊗ Δ^c) ∘ Δ^c`. -/
private noncomputable def coassocRHSAlgC (τ : UnorderedTree (α' ⊕ β') → β') :
    ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R']
      ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
          ConnesKreimer R' (UnorderedTree (α' ⊕ β'))) :=
  (Algebra.TensorProduct.map (AlgHom.id R' _) (traceComulAlgHom (R := R') τ)).comp
    (traceComulAlgHom τ)

/-- `Δ^c` is coassociative for a coherent trace encoder. On each tree both composites enumerate
the pairs of nested cuts; the forest case follows since both are algebra homomorphisms. -/
theorem traceComul_coassoc
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))) ∘ₗ
      (traceComulAlgHom (R := R') τ).toLinearMap.rTensor _ ∘ₗ
      (traceComulAlgHom (R := R') τ).toLinearMap =
    (traceComulAlgHom (R := R') τ).toLinearMap.lTensor _ ∘ₗ
      (traceComulAlgHom (R := R') τ).toLinearMap := by
  suffices hLR : coassocLHSAlgC (R' := R') τ = coassocRHSAlgC τ from
    congrArg AlgHom.toLinearMap hLR
  refine ConnesKreimer.algHom_ext_ofTree fun T ↦ ?_
  show TensorProduct.assoc R' _ _ _
      ((traceComulAlgHom (R := R') τ).toLinearMap.rTensor _
        (traceComulAlgHom (R := R') τ (ConnesKreimer.ofTree T))) =
    (traceComulAlgHom (R := R') τ).toLinearMap.lTensor _
      (traceComulAlgHom (R := R') τ (ConnesKreimer.ofTree T))
  rw [traceComulAlgHom_apply_ofTree]
  exact traceComul_coassoc_tree τ hτ T

end CoassocCommRing

/-! ### Counit laws and the bialgebra

The counit laws follow from the uniqueness of the empty cut (`traceCuts_filter_empty`). -/

section BialgebraInst
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- The AlgHom form of Δ^c coassociativity under trace coherence. -/
theorem traceComulAlgHom_coassoc_algHom
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    (Algebra.TensorProduct.assoc R' R' R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).toAlgHom.comp
      ((Algebra.TensorProduct.map (traceComulAlgHom (R := R') τ) (AlgHom.id R' _)).comp
        (traceComulAlgHom (R := R') τ)) =
    (Algebra.TensorProduct.map (AlgHom.id R' _) (traceComulAlgHom (R := R') τ)).comp
      (traceComulAlgHom (R := R') τ) := by
  apply AlgHom.toLinearMap_injective
  -- The .toLinearMap of both AlgHom expressions equals the corresponding
  -- LinearMap composition. `traceComul_coassoc` gives the equality.
  exact traceComul_coassoc τ hτ

end BialgebraInst

/-! ### Counit laws on trees and forests

As for the Connes–Kreimer coproduct, the laws are proved on trees and extended to forests
multiplicatively, over a commutative semiring. -/

section CounitLaws
variable {R' : Type*} [CommSemiring R'] {α' β' : Type*}

private theorem counit_rTensor_comulTree (τ : UnorderedTree (α' ⊕ β') → β')
    (T : UnorderedTree (α' ⊕ β')) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
      (comulTreeOfCuts (traceCuts τ) T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T := by
  -- Expand comulTreeOfCuts (traceCuts τ) T.
  unfold comulTreeOfCuts
  rw [map_add]
  -- First summand: (counit ⊗ id)(ofTree T ⊗ 1) = counit(ofTree T) ⊗ 1 = 0 ⊗ 1 = 0.
  rw [show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
              (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
            (ConnesKreimer.ofTree T ⊗ₜ[R']
              (1 : ConnesKreimer R' (UnorderedTree (α' ⊕ β')))) = 0 from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_ofTree,
        TensorProduct.zero_tmul]]
  rw [zero_add]
  -- Distribute (counit ⊗ id) through the multiset sum.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))]
  simp only [Multiset.map_map]
  -- Each summand: (counit ⊗ id)(of' p.1 ⊗ ofTree p.2) =
  --   (if p.1.card = 0 then 1 else 0) ⊗ ofTree p.2.
  rw [show ((Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
              (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))) ∘
            (fun p : Forest (UnorderedTree (α' ⊕ β')) × UnorderedTree (α' ⊕ β') =>
              ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2)) =
            (fun p => (if p.1.card = 0 then (1 : R') else 0) ⊗ₜ[R']
                       ConnesKreimer.ofTree p.2) from by
    funext p
    show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
            (AlgHom.id R' _))
          (ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_of']]
  -- Pull the if outside the tensor product: (if h then 1 else 0) ⊗ y = if h then 1 ⊗ y else 0.
  rw [show (fun p : Forest (UnorderedTree (α' ⊕ β')) × UnorderedTree (α' ⊕ β') =>
              (if p.1.card = 0 then (1 : R') else 0) ⊗ₜ[R']
                ConnesKreimer.ofTree p.2) =
            (fun p =>
              if p.1.card = 0 then
                ((1 : R') ⊗ₜ[R'] ConnesKreimer.ofTree p.2 :
                  R' ⊗[R'] ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
              else 0) from by
    funext p
    by_cases hp : p.1.card = 0
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp, TensorProduct.zero_tmul]]
  rw [← Multiset.sum_map_filter]
  -- Filter equals {(0, T)} by traceCuts_filter_empty.
  rw [ConnesKreimer.traceCuts_filter_empty τ T,
      Multiset.map_singleton, Multiset.sum_singleton]

private theorem counit_lTensor_comulTree (τ : UnorderedTree (α' ⊕ β') → β')
    (T : UnorderedTree (α' ⊕ β')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
      (comulTreeOfCuts (traceCuts τ) T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R') := by
  unfold comulTreeOfCuts
  rw [map_add]
  -- First summand: (id ⊗ counit)(ofTree T ⊗ 1) = ofTree T ⊗ counit(1) = ofTree T ⊗ 1.
  rw [show (Algebra.TensorProduct.map
              (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
              ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
            (ConnesKreimer.ofTree T ⊗ₜ[R']
              (1 : ConnesKreimer R' (UnorderedTree (α' ⊕ β')))) =
          ConnesKreimer.ofTree T ⊗ₜ[R'] (1 : R') from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]]
  -- Second summand: distribute via map_multiset_sum, then show the entire sum is 0.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))]
  simp only [Multiset.map_map]
  -- Each summand: (id ⊗ counit)(of' p.1 ⊗ ofTree p.2) = of' p.1 ⊗ counit(ofTree p.2)
  --              = of' p.1 ⊗ 0 = 0.
  rw [show ((Algebra.TensorProduct.map
              (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
              ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')) ∘
            (fun p : Forest (UnorderedTree (α' ⊕ β')) × UnorderedTree (α' ⊕ β') =>
              ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2)) =
            (fun _ => (0 : ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R'] R')) from by
    funext p
    show (Algebra.TensorProduct.map
            (AlgHom.id R' _) ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
          (ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_ofTree,
        TensorProduct.tmul_zero]]
  -- The sum of all zeros over a multiset is 0.
  rw [show ((traceCuts τ T).map
      (fun _ : Forest (UnorderedTree (α' ⊕ β')) × UnorderedTree (α' ⊕ β') =>
        (0 : ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R'] R'))).sum = 0 from by
    induction (traceCuts τ T) using Multiset.induction with
    | empty => simp
    | cons _ _ ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, add_zero]]
  rw [add_zero]

private theorem counit_rTensor_comulForest (τ : UnorderedTree (α' ⊕ β') → β')
    (F : Forest (UnorderedTree (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
        (comulTreeOfCuts (traceCuts τ) T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
      (comulForestOfCuts (R := R') (traceCuts τ) F) = (1 : R') ⊗ₜ ConnesKreimer.of' F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestOfCuts_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') :=
      (ConnesKreimer.of'_cons T F').symm
    rw [comulForestOfCuts_cons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hForest]

private theorem counit_lTensor_comulForest (τ : UnorderedTree (α' ⊕ β') → β')
    (F : Forest (UnorderedTree (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
        (comulTreeOfCuts (traceCuts τ) T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
      (comulForestOfCuts (R := R') (traceCuts τ) F) = ConnesKreimer.of' F ⊗ₜ (1 : R') := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestOfCuts_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') :=
      (ConnesKreimer.of'_cons T F').symm
    rw [comulForestOfCuts_cons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, hForest]

/-- The right counit law for Δ^c. -/
theorem counit_rTensor_traceComulAlgHom (τ : UnorderedTree (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' _)).comp (traceComulAlgHom (R := R') τ) =
      (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
        (traceComulAlgHom (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [traceComulAlgHom_apply_of', Algebra.TensorProduct.lid_symm_apply]
  exact counit_rTensor_comulForest τ F (fun T _ => counit_rTensor_comulTree τ T)

/-- The left counit law for Δ^c. -/
theorem counit_lTensor_traceComulAlgHom (τ : UnorderedTree (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map (AlgHom.id R' _)
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')).comp
        (traceComulAlgHom (R := R') τ) =
      (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
        (traceComulAlgHom (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [traceComulAlgHom_apply_of', Algebra.TensorProduct.rid_symm_apply]
  exact counit_lTensor_comulForest τ F (fun T _ => counit_lTensor_comulTree τ T)

/-- `Δ^c` is the admissible-cut coproduct at the cuts `traceCuts τ`. -/
theorem traceComulAlgHom_eq_comulOfCuts {R : Type*} [CommSemiring R]
    (τ : UnorderedTree (α' ⊕ β') → β') :
    traceComulAlgHom (R := R) τ = comulOfCuts (R := R) (traceCuts τ) := rfl

/-- For a coherent trace encoder, `traceCuts τ` is an admissible cut policy, so
`WithCuts R (traceCuts τ)` is a bialgebra, as in Marcolli, Chomsky and Berwick's Lemma 1.2.10.
Coherence enters through `Fact`, since instance search cannot find the hypothesis otherwise. -/
instance instIsBialgebraCutsTraceCuts (τ : UnorderedTree (α' ⊕ β') → β')
    [Fact (TraceCoherent τ)] :
    IsBialgebraCuts (traceCuts τ) where
  coassoc := by
    intro R _
    rw [← traceComulAlgHom_eq_comulOfCuts]
    exact traceComulAlgHom_coassoc_algHom τ Fact.out
  counit_rTensor := by
    intro R _
    exact counit_rTensor_traceComulAlgHom τ
  counit_lTensor := by
    intro R _
    exact counit_lTensor_traceComulAlgHom τ

/-- A coherent trace encoder gives the bialgebra of `Δ^c` by instance search. -/
noncomputable example {R : Type*} [CommRing R]
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    Bialgebra R (WithCuts R (traceCuts τ)) :=
  haveI : Fact (TraceCoherent τ) := ⟨hτ⟩
  inferInstance

end CounitLaws

end ConnesKreimer
