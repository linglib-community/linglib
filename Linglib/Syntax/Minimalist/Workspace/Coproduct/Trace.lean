/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceCut
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

* `ConnesKreimer.doubleCutsCrown_traceCuts`: for a coherent encoder, nested trace cuts can be
  taken in either order.
* `ConnesKreimer.traceComulAlgHom_coassoc`: `Δ^c` is coassociative for a coherent encoder.
* `ConnesKreimer.instIsBialgebraCutsTraceCuts`: the trace cuts are an admissible policy, which
  gives `WithCuts R (traceCuts τ)` its `Bialgebra` instance.

## Implementation notes

The bialgebra laws are those of the generic coproduct of `Coproduct/WithCuts.lean`. Its
coassociativity asks that the two enumerations of nested cuts agree, which
`Core/Combinatorics/RootedTree/DoubleCut.lean` proves for every coherent extraction policy; the
trace policy is coherent exactly under trace coherence (`extractCoherent_leaveTrace`).

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

/-! ### The bialgebra

Under trace coherence nested trace cuts can be taken in either order, which is the combinatorial
core of Marcolli, Chomsky and Berwick's Lemma 1.2.10, and the empty cut is the only trace cut with
an empty crown (`traceCuts_filter_empty`). -/

/-- Under trace coherence the double trace cuts through the crown are those through the trunk. -/
theorem doubleCutsCrown_traceCuts {τ : UnorderedTree (α ⊕ β) → β} (hτ : TraceCoherent τ)
    (T : UnorderedTree (α ⊕ β)) :
    doubleCutsCrown (traceCuts τ) T = doubleCutsTrunk (traceCuts τ) T :=
  doubleCutsCrown_eq_doubleCutsTrunk _ (traceCuts_mk τ)
    (extractCoherent_leaveTrace fun t p hp ↦
      hτ (.mk t) (projCut p) (Multiset.mem_map.mpr ⟨p, hp, rfl⟩)) T

/-- `Δ^c` is coassociative for a coherent trace encoder. -/
theorem traceComulAlgHom_coassoc {τ : UnorderedTree (α ⊕ β) → β} (hτ : TraceCoherent τ) :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree (α ⊕ β))) _ _).toAlgHom.comp
        ((Algebra.TensorProduct.map (traceComulAlgHom (R := R) τ) (.id R _)).comp
          (traceComulAlgHom τ)) =
      (Algebra.TensorProduct.map (.id R _) (traceComulAlgHom (R := R) τ)).comp
        (traceComulAlgHom τ) :=
  comulOfCuts_coassoc (doubleCutsCrown_traceCuts hτ)

/-- For a coherent trace encoder, `traceCuts τ` is an admissible cut policy, so
`WithCuts R (traceCuts τ)` is a bialgebra, as in Marcolli, Chomsky and Berwick's Lemma 1.2.10.
Coherence enters through `Fact`, since instance search cannot find the hypothesis otherwise. -/
instance instIsBialgebraCutsTraceCuts (τ : UnorderedTree (α ⊕ β) → β) [Fact (TraceCoherent τ)] :
    IsBialgebraCuts (traceCuts τ) where
  doubleCutsCrown_eq := doubleCutsCrown_traceCuts Fact.out
  filter_card_eq_zero := traceCuts_filter_empty τ

/-- A coherent trace encoder gives the bialgebra of `Δ^c` by instance search. -/
noncomputable example (τ : UnorderedTree (α ⊕ β) → β) (hτ : TraceCoherent τ) :
    Bialgebra R (WithCuts R (traceCuts τ)) :=
  haveI : Fact (TraceCoherent τ) := ⟨hτ⟩
  inferInstance

end ConnesKreimer
