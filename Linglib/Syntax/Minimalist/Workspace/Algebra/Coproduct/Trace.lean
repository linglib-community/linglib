/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Multiset
public import Linglib.Syntax.Minimalist.Coproduct.DoubleCut
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

* `ConnesKreimer.comulCAlgHomN`: `Δ^c` as an algebra homomorphism, for a trace encoder `τ`.
* `ConnesKreimer.TraceCoherent`: `τ` gives a cut trunk the same marker as the tree it was cut
  from.

## Main results

* `ConnesKreimer.comulCN_coassoc`: `Δ^c` is coassociative for a coherent encoder.
* `ConnesKreimer.instIsAdmissibleCutsCN`: the counit laws and coassociativity, which give
  `WithCuts R (cutSummandsCN τ)` its `Bialgebra` instance.

## Implementation notes

Coassociativity is proved directly: both composites enumerate pairs of nested admissible cuts,
and the two enumerations agree under trace coherence (`DoubleCut.coassT`). The pairing duality
that gives coassociativity of the pruning coproduct in `Coproduct/PruningDuality.lean` fails
here, because grafting never removes trace markers.

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
`cutSummandsCN τ`. -/

/-- `comulCTreeN τ` is `Δ^c` on a single tree, `comulTreeNG` at the cuts `cutSummandsCN τ`. -/
noncomputable def comulCTreeN (τ : UnorderedTree (α ⊕ β) → β) :
    UnorderedTree (α ⊕ β) →
      ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  comulTreeNG (cutSummandsCN τ)

/-- `comulCForestN τ` is `Δ^c` on a forest, the product over its trees. -/
noncomputable def comulCForestN (τ : UnorderedTree (α ⊕ β) → β) :
    Forest (UnorderedTree (α ⊕ β)) →
      ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  comulForestNG (cutSummandsCN τ)

@[simp] theorem comulCForestN_zero (τ : UnorderedTree (α ⊕ β) → β) :
    comulCForestN (R := R) τ (0 : Forest (UnorderedTree (α ⊕ β))) = 1 :=
  comulForestNG_zero _

@[simp] theorem comulCForestN_add (τ : UnorderedTree (α ⊕ β) → β)
    (F G : Forest (UnorderedTree (α ⊕ β))) :
    comulCForestN (R := R) τ (F + G) =
      comulCForestN (R := R) τ F * comulCForestN (R := R) τ G :=
  comulForestNG_add _ F G

/-- `comulCAlgHomN τ` is the coproduct `Δ^c` on `ConnesKreimer R (UnorderedTree (α ⊕ β))`, an
algebra homomorphism, for the trace encoder `τ`. -/
noncomputable def comulCAlgHomN (τ : UnorderedTree (α ⊕ β) → β) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  comulAlgHomNG (cutSummandsCN τ)

@[simp] theorem comulCAlgHomN_apply_of' (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (UnorderedTree (α ⊕ β))) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.of' F) = comulCForestN τ F :=
  comulAlgHomNG_apply_of' _ F

@[simp] theorem comulCAlgHomN_apply_ofTree (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.ofTree T) = comulCTreeN τ T :=
  comulAlgHomNG_apply_ofTree _ T

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
  ∀ T : UnorderedTree (α ⊕ β), ∀ p ∈ cutSummandsCN τ T, τ p.2 = τ T

/-- Constant trace encoders are coherent. -/
theorem traceCoherent_const (b : β) :
    TraceCoherent (fun _ : UnorderedTree (α ⊕ β) => b) :=
  fun _ _ _ => rfl

/-! ### Enumerating pairs of nested cuts

Both `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` sum over pairs of nested admissible cuts of a tree.
This section writes `Δ^c` as a sum over cut enumerators (`treeCutsN`, `forestCutsN`) and each
composite as a sum over a double-cut enumerator (`dcLHS`, `dcRHS`). -/

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

/-- `treeCutsN τ T` lists the cut summands of `T` as pairs of a crown forest and a trunk forest,
namely the full cut `({T}, ∅)` and each proper or empty cut with its one-tree trunk. -/
private noncomputable def treeCutsN (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    Multiset (Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β))) :=
  treeCutsG (cutSummandsCN τ) T

/-- `comulCTreeN` is a sum over `treeCutsN`. -/
private theorem comulCTreeN_eq_sum (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    comulCTreeN (R := R) τ T = ((treeCutsN τ T).map (cutTensor (R := R))).sum :=
  comulTreeNG_eq_sum _ T

/-- `forestCutsN τ F` lists the cut summands of the forest `F`. -/
private noncomputable def forestCutsN (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (UnorderedTree (α ⊕ β))) :
    Multiset (Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β))) :=
  forestCutsG (cutSummandsCN τ) F

private theorem forestCutsN_zero (τ : UnorderedTree (α ⊕ β) → β) :
    forestCutsN τ (0 : Forest (UnorderedTree (α ⊕ β))) = {(0, 0)} :=
  forestCutsG_zero _

private theorem forestCutsN_cons (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) (F : Forest (UnorderedTree (α ⊕ β))) :
    forestCutsN τ (T ::ₘ F) =
      (treeCutsN τ T ×ˢ forestCutsN τ F).map ConnesKreimer.combinerProjG :=
  forestCutsG_cons _ T F

/-- `comulCForestN` is a sum over `forestCutsN`. -/
private theorem comulCForestN_eq_sum (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (UnorderedTree (α ⊕ β))) :
    comulCForestN (R := R) τ F = ((forestCutsN τ F).map (cutTensor (R := R))).sum :=
  comulForestNG_eq_sum _ F

/-- `dcLHS τ T` cuts `T` and then cuts the crown again. -/
private noncomputable def dcLHS (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    Multiset (Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β)) ×
              Forest (UnorderedTree (α ⊕ β))) :=
  (treeCutsN τ T).bind (fun AB =>
    (forestCutsN τ AB.1).map (fun A12 => (A12.1, A12.2, AB.2)))

/-- `dcRHS τ T` cuts `T` and then cuts the trunk again. -/
private noncomputable def dcRHS (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    Multiset (Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β)) ×
              Forest (UnorderedTree (α ⊕ β))) :=
  (treeCutsN τ T).bind (fun AB =>
    (forestCutsN τ AB.2).map (fun B12 => (AB.1, B12.1, B12.2)))

/-- Cutting the crown of one cut pair again enumerates the crown's forest cuts. -/
private theorem lhs_per_pair (τ : UnorderedTree (α ⊕ β) → β)
    (A B : Forest (UnorderedTree (α ⊕ β))) :
    (TensorProduct.assoc R (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β))) (ConnesKreimer R (UnorderedTree (α ⊕ β))))
        (comulCForestN (R := R) τ A ⊗ₜ[R] ConnesKreimer.of' B) =
      ((forestCutsN τ A).map
        (fun A12 => tripleTensor (R := R) (A12.1, A12.2, B))).sum := by
  rw [comulCForestN_eq_sum]
  let φ : (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
                ConnesKreimer R (UnorderedTree (α ⊕ β))) :=
    (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
      ((TensorProduct.mk R _ _).flip (ConnesKreimer.of' B))
  show φ ((Multiset.map (cutTensor (R := R)) (forestCutsN τ A)).sum) = _
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
    ConnesKreimer.of' (R := R) A ⊗ₜ[R] comulCForestN (R := R) τ B =
      ((forestCutsN τ B).map
        (fun B12 => tripleTensor (R := R) (A, B12.1, B12.2))).sum := by
  rw [comulCForestN_eq_sum]
  let ψ : (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R] ConnesKreimer R (UnorderedTree (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
                ConnesKreimer R (UnorderedTree (α ⊕ β))) :=
    (TensorProduct.mk R _ _) (ConnesKreimer.of' A)
  show ψ ((Multiset.map (cutTensor (R := R)) (forestCutsN τ B)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  rfl

/-- The composite `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c` on a tree sums the `dcLHS`
    enumeration. -/
private theorem lhsExpand (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    (TensorProduct.assoc R (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β))) (ConnesKreimer R (UnorderedTree (α ⊕ β))))
        ((comulCAlgHomN (R := R) τ).toLinearMap.rTensor _ (comulCTreeN τ T)) =
      ((dcLHS τ T).map (tripleTensor (R := R))).sum := by
  rw [comulCTreeN_eq_sum]
  let Λ := (TensorProduct.assoc R (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β)))
        (ConnesKreimer R (UnorderedTree (α ⊕ β)))).toLinearMap ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap.rTensor
        (ConnesKreimer R (UnorderedTree (α ⊕ β)))
  show Λ ((Multiset.map (cutTensor (R := R)) (treeCutsN τ T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold dcLHS
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show Λ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCutsN τ A).map (fun A12 => (A12.1, A12.2, B)))).sum
  rw [Multiset.map_map]
  show (TensorProduct.assoc R _ _ _)
      ((comulCAlgHomN (R := R) τ).toLinearMap.rTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B)) = _
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, comulCAlgHomN_apply_of',
      lhs_per_pair]
  rfl

/-- The composite `(id ⊗ Δ^c) ∘ Δ^c` on a tree sums the `dcRHS` enumeration. -/
private theorem rhsExpand (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ (comulCTreeN τ T) =
      ((dcRHS τ T).map (tripleTensor (R := R))).sum := by
  rw [comulCTreeN_eq_sum]
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _
        ((Multiset.map (cutTensor (R := R)) (treeCutsN τ T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold dcRHS
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCutsN τ B).map (fun B12 => (A, B12.1, B12.2)))).sum
  rw [Multiset.map_map]
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B) = _
  rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, comulCAlgHomN_apply_of',
      rhs_per_pair]
  rfl

/-! ### Descent of the double-cut enumerators

The enumerators `dcLHS` and `dcRHS` are the images under `UnorderedTree.mk` of the planar
`DoubleCut.dcLHSP` and `DoubleCut.dcRHSP`, which `DoubleCut.coassT` identifies. -/

/-- Project a tree-level (crown, trunk) pair to UnorderedTree. -/
private def projPair (p : Forest (RoseTree (α ⊕ β)) × Forest (RoseTree (α ⊕ β))) :
    Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β)) :=
  (p.1.map UnorderedTree.mk, p.2.map UnorderedTree.mk)

private theorem treeCutsN_mk (τ : UnorderedTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    treeCutsN τ (UnorderedTree.mk t)
      = (DoubleCut.treeCutsP (τ ∘ UnorderedTree.mk) t).map projPair := by
  unfold treeCutsN treeCutsG DoubleCut.treeCutsP
  rw [cutSummandsCN_mk, Multiset.map_cons, Multiset.map_map, Multiset.map_map]
  congr 1

/-- Naturality of the cut combiner under `projPair`. -/
private theorem combinerProjG_nat
    (A B : Multiset (Forest (RoseTree (α ⊕ β)) × Forest (RoseTree (α ⊕ β)))) :
    ((A.map projPair) ×ˢ (B.map projPair)).map ConnesKreimer.combinerProjG
      = ((A ×ˢ B).map (fun pq => (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2))).map projPair := by
  rw [← Multiset.prodMap_map_product, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨⟨F1, m1⟩, ⟨F2, m2⟩⟩ _
  show ConnesKreimer.combinerProjG
      ((F1.map UnorderedTree.mk, m1.map UnorderedTree.mk), (F2.map UnorderedTree.mk,
        m2.map UnorderedTree.mk))
    = projPair (F1 + F2, m1 + m2)
  show (F1.map UnorderedTree.mk + F2.map UnorderedTree.mk,
    m1.map UnorderedTree.mk + m2.map UnorderedTree.mk)
      = ((F1 + F2).map UnorderedTree.mk, (m1 + m2).map UnorderedTree.mk)
  rw [Multiset.map_add, Multiset.map_add]

private theorem forestCutsN_mk (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (RoseTree (α ⊕ β))) :
    forestCutsN τ (F.map UnorderedTree.mk)
      = (DoubleCut.forestCutsP (τ ∘ UnorderedTree.mk) F).map projPair := by
  induction F using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, forestCutsN_zero, DoubleCut.forestCutsP_zero,
        Multiset.map_singleton]; rfl
  | cons t F ih =>
    rw [Multiset.map_cons, forestCutsN_cons, treeCutsN_mk, ih, DoubleCut.forestCutsP_cons,
        DoubleCut.convFP_eq, combinerProjG_nat]

private theorem dcLHS_mk (τ : UnorderedTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcLHS τ (UnorderedTree.mk t) = (DoubleCut.dcLHSP
      (τ ∘ UnorderedTree.mk) t).map DoubleCut.proj3 := by
  unfold dcLHS DoubleCut.dcLHSP
  rw [treeCutsN_mk, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; rintro ⟨F, G⟩ _
  show (forestCutsN τ (F.map UnorderedTree.mk)).map (fun A12 => (A12.1, A12.2,
    G.map UnorderedTree.mk))
      = ((DoubleCut.forestCutsP (τ ∘ UnorderedTree.mk) F).map
          (fun A12 => (A12.1, A12.2, G))).map DoubleCut.proj3
  rw [forestCutsN_mk, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨A1, A2⟩ _; rfl

private theorem dcRHS_mk (τ : UnorderedTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcRHS τ (UnorderedTree.mk t) = (DoubleCut.dcRHSP
      (τ ∘ UnorderedTree.mk) t).map DoubleCut.proj3 := by
  unfold dcRHS DoubleCut.dcRHSP
  rw [treeCutsN_mk, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; rintro ⟨F, G⟩ _
  show (forestCutsN τ (G.map UnorderedTree.mk)).map (fun B12 => (F.map UnorderedTree.mk, B12.1,
    B12.2))
      = ((DoubleCut.forestCutsP (τ ∘ UnorderedTree.mk) G).map
          (fun B12 => (F, B12.1, B12.2))).map DoubleCut.proj3
  rw [forestCutsN_mk, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨B1, B2⟩ _; rfl

/-- The tree-level trace coherence descends from the UnorderedTree one. -/
private theorem traceCoherentP_of_coherent (τ : UnorderedTree (α ⊕ β) → β)
    (hτ : TraceCoherent τ) : DoubleCut.TraceCoherentP (τ ∘ UnorderedTree.mk) := by
  intro t p hp
  have hmem : ConnesKreimer.projSummand p ∈ cutSummandsCN τ (UnorderedTree.mk t) := by
    rw [cutSummandsCN_mk]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩
  exact hτ (UnorderedTree.mk t) (ConnesKreimer.projSummand p) hmem

/-- Under trace coherence the two double-cut enumerators of a tree agree, the combinatorial core
of Marcolli, Chomsky and Berwick's Lemma 1.2.10. -/
private theorem doubleCut_eq (τ : UnorderedTree (α ⊕ β) → β)
    (hτ : TraceCoherent τ) (T : UnorderedTree (α ⊕ β)) :
    dcLHS τ T = dcRHS τ T := by
  induction T using Quotient.inductionOn with
  | _ t =>
    show dcLHS τ (UnorderedTree.mk t) = dcRHS τ (UnorderedTree.mk t)
    rw [dcLHS_mk, dcRHS_mk,
        DoubleCut.coassT (τ ∘ UnorderedTree.mk) (traceCoherentP_of_coherent τ hτ) t]

end DoubleCut

/-! ### Coassociativity

The statements are over a commutative ring for the `Bialgebra` consumers; the proof itself works
over a commutative semiring. -/

section CoassocCommRing
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- On a tree, both composites enumerate the pairs of nested admissible cuts of `T`, and
`TraceCoherent τ` makes the markers written by the two cut orders agree. -/
theorem comulCN_coassoc_tree
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ)
    (T : UnorderedTree (α' ⊕ β')) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        ((comulCAlgHomN (R := R') τ).toLinearMap.rTensor _ (comulCTreeN τ T)) =
      (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _ (comulCTreeN τ T) := by
  rw [lhsExpand, rhsExpand, doubleCut_eq τ hτ T]

/-- `coassocLHSAlgC τ` is `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c`. -/
private noncomputable def coassocLHSAlgC (τ : UnorderedTree (α' ⊕ β') → β') :
    ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R']
      ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
          ConnesKreimer R' (UnorderedTree (α' ⊕ β'))) :=
  (Algebra.TensorProduct.assoc R' R' R' _ _ _).toAlgHom.comp
    ((Algebra.TensorProduct.map (comulCAlgHomN (R := R') τ)
      (AlgHom.id R' _)).comp (comulCAlgHomN τ))

/-- `coassocRHSAlgC τ` is `(id ⊗ Δ^c) ∘ Δ^c`. -/
private noncomputable def coassocRHSAlgC (τ : UnorderedTree (α' ⊕ β') → β') :
    ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R']
      ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R']
          ConnesKreimer R' (UnorderedTree (α' ⊕ β'))) :=
  (Algebra.TensorProduct.map (AlgHom.id R' _) (comulCAlgHomN (R := R') τ)).comp
    (comulCAlgHomN τ)

/-- `Δ^c` is coassociative for a coherent trace encoder. On each tree both composites enumerate
the pairs of nested cuts; the forest case follows since both are algebra homomorphisms. -/
theorem comulCN_coassoc
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))) ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap.rTensor _ ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap =
    (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _ ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap := by
  suffices hLR : coassocLHSAlgC (R' := R') τ = coassocRHSAlgC τ from
    congrArg AlgHom.toLinearMap hLR
  refine ConnesKreimer.algHom_ext_ofTree fun T ↦ ?_
  show TensorProduct.assoc R' _ _ _
      ((comulCAlgHomN (R := R') τ).toLinearMap.rTensor _
        (comulCAlgHomN (R := R') τ (ConnesKreimer.ofTree T))) =
    (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _
      (comulCAlgHomN (R := R') τ (ConnesKreimer.ofTree T))
  rw [comulCAlgHomN_apply_ofTree]
  exact comulCN_coassoc_tree τ hτ T

end CoassocCommRing

/-! ### Counit laws and the bialgebra

The counit laws follow from the uniqueness of the empty cut (`cutSummandsCN_filter_empty`). -/

section BialgebraInst
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- The AlgHom form of Δ^c coassociativity under trace coherence. -/
theorem comulCAlgHomN_coassoc_algHom
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    (Algebra.TensorProduct.assoc R' R' R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulCAlgHomN (R := R') τ) (AlgHom.id R' _)).comp
        (comulCAlgHomN (R := R') τ)) =
    (Algebra.TensorProduct.map (AlgHom.id R' _) (comulCAlgHomN (R := R') τ)).comp
      (comulCAlgHomN (R := R') τ) := by
  apply AlgHom.toLinearMap_injective
  -- The .toLinearMap of both AlgHom expressions equals the corresponding
  -- LinearMap composition. `comulCN_coassoc` gives the equality.
  exact comulCN_coassoc τ hτ

end BialgebraInst

/-! ### Counit laws on trees and forests

As for the pruning coproduct, the laws are proved on trees and extended to forests
multiplicatively, over a commutative semiring. -/

section CounitLaws
variable {R' : Type*} [CommSemiring R'] {α' β' : Type*}

private theorem counit_rTensor_comulCTreeN (τ : UnorderedTree (α' ⊕ β') → β')
    (T : UnorderedTree (α' ⊕ β')) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
      (comulCTreeN τ T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T := by
  -- Expand comulCTreeN τ T.
  unfold comulCTreeN comulTreeNG
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
  -- Filter equals {(0, T)} by cutSummandsCN_filter_empty.
  rw [ConnesKreimer.cutSummandsCN_filter_empty τ T,
      Multiset.map_singleton, Multiset.sum_singleton]

private theorem counit_lTensor_comulCTreeN (τ : UnorderedTree (α' ⊕ β') → β')
    (T : UnorderedTree (α' ⊕ β')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
      (comulCTreeN τ T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R') := by
  unfold comulCTreeN comulTreeNG
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
  rw [show ((cutSummandsCN τ T).map
      (fun _ : Forest (UnorderedTree (α' ⊕ β')) × UnorderedTree (α' ⊕ β') =>
        (0 : ConnesKreimer R' (UnorderedTree (α' ⊕ β')) ⊗[R'] R'))).sum = 0 from by
    induction (cutSummandsCN τ T) using Multiset.induction with
    | empty => simp
    | cons _ _ ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, add_zero]]
  rw [add_zero]

private theorem counit_rTensor_comulCForestN (τ : UnorderedTree (α' ⊕ β') → β')
    (F : Forest (UnorderedTree (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
        (comulCTreeN τ T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
      (comulCForestN (R := R') τ F) = (1 : R') ⊗ₜ ConnesKreimer.of' F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') :=
      (ConnesKreimer.of'_cons T F').symm
    -- comulCForestN (T ::ₘ F') = comulCTreeN τ T * comulCForestN τ F'
    have hCons : comulCForestN (R := R') τ (T ::ₘ F') =
        comulCTreeN (R := R') τ T * comulCForestN (R := R') τ F' :=
      comulForestNG_cons _ T F'
    rw [hCons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hForest]

private theorem counit_lTensor_comulCForestN (τ : UnorderedTree (α' ⊕ β') → β')
    (F : Forest (UnorderedTree (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map
        (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
        (comulCTreeN τ T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
      (comulCForestN (R := R') τ F) = ConnesKreimer.of' F ⊗ₜ (1 : R') := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (UnorderedTree (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') :=
      (ConnesKreimer.of'_cons T F').symm
    have hCons : comulCForestN (R := R') τ (T ::ₘ F') =
        comulCTreeN (R := R') τ T * comulCForestN (R := R') τ F' :=
      comulForestNG_cons _ T F'
    rw [hCons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, hForest]

/-- The right counit law for Δ^c. -/
theorem counit_rTensor_comulCAlgHomN (τ : UnorderedTree (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' _)).comp (comulCAlgHomN (R := R') τ) =
      (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))))
        (comulCAlgHomN (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [comulCAlgHomN_apply_of', Algebra.TensorProduct.lid_symm_apply]
  exact counit_rTensor_comulCForestN τ F (fun T _ => counit_rTensor_comulCTreeN τ T)

/-- The left counit law for Δ^c. -/
theorem counit_lTensor_comulCAlgHomN (τ : UnorderedTree (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map (AlgHom.id R' _)
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R')).comp (comulCAlgHomN (R := R') τ) =
      (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (UnorderedTree (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (UnorderedTree (α' ⊕ β')) →ₐ[R'] R'))
        (comulCAlgHomN (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (UnorderedTree (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [comulCAlgHomN_apply_of', Algebra.TensorProduct.rid_symm_apply]
  exact counit_lTensor_comulCForestN τ F (fun T _ => counit_lTensor_comulCTreeN τ T)

/-- `Δ^c` is the admissible-cut coproduct at the cuts `cutSummandsCN τ`. -/
theorem comulCAlgHomN_eq_G {R : Type*} [CommSemiring R] (τ : UnorderedTree (α' ⊕ β') → β') :
    comulCAlgHomN (R := R) τ = comulAlgHomNG (R := R) (cutSummandsCN τ) := rfl

/-- For a coherent trace encoder, `cutSummandsCN τ` is an admissible cut policy, so
`WithCuts R (cutSummandsCN τ)` is a bialgebra, as in Marcolli, Chomsky and Berwick's Lemma 1.2.10.
Coherence enters through `Fact`, since instance search cannot find the hypothesis otherwise. -/
instance instIsAdmissibleCutsCN (τ : UnorderedTree (α' ⊕ β') → β')
    [Fact (TraceCoherent τ)] :
    IsAdmissibleCuts (cutSummandsCN τ) where
  coassoc := by
    intro R _
    rw [← comulCAlgHomN_eq_G]
    exact comulCAlgHomN_coassoc_algHom τ Fact.out
  counit_rTensor := by
    intro R _
    exact counit_rTensor_comulCAlgHomN τ
  counit_lTensor := by
    intro R _
    exact counit_lTensor_comulCAlgHomN τ

/-- A coherent trace encoder gives the bialgebra of `Δ^c` by instance search. -/
noncomputable example {R : Type*} [CommRing R]
    (τ : UnorderedTree (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    Bialgebra R (WithCuts R (cutSummandsCN τ)) :=
  haveI : Fact (TraceCoherent τ) := ⟨hτ⟩
  inferInstance

end CounitLaws

end ConnesKreimer
