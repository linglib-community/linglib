/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

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
* `ConnesKreimer.instIsBialgebraCutsTraceCuts`: coassociativity and the right counit law, which
  give `WithCuts R (traceCuts τ)` its `Bialgebra` instance.

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

/-! ### The bialgebra

The right counit law follows from the uniqueness of the empty cut (`traceCuts_filter_empty`), and
the left one holds at every cut enumeration. -/

section Bialgebra
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
      (traceComulAlgHom (R := R') τ) :=
  AlgHom.toLinearMap_injective (traceComul_coassoc τ hτ)

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
  coassoc _ _ := traceComulAlgHom_coassoc_algHom τ Fact.out
  rTensor_counit_comp_comul _ _ := rTensor_counit_comp_comulOfCuts (traceCuts_filter_empty τ)

/-- A coherent trace encoder gives the bialgebra of `Δ^c` by instance search. -/
noncomputable example {R : Type*} [CommRing R]
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    Bialgebra R (WithCuts R (traceCuts τ)) :=
  haveI : Fact (TraceCoherent τ) := ⟨hτ⟩
  inferInstance

end Bialgebra

end ConnesKreimer
