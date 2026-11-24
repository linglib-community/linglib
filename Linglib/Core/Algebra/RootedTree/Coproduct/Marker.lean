/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.MarkerCut
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# The marker coproduct

On forests of trees whose vertices are labelled in `α ⊕ β`, the marker coproduct sums over the
marker cuts of a tree, pairing the cut subtrees with the trunk, in which each cut subtree `S` has
left the marker leaf `inr (τ S)`. It is the coproduct of `Coproduct/WithCuts.lean` at the
enumeration `markerCuts τ`, and it is coassociative when `τ` gives a trunk the marker of the tree
it was cut from, so that disjoint union and the marker coproduct make a bialgebra, graded by the
number of edges.

## Main definitions

* `ConnesKreimer.markerComulAlgHom`: the marker coproduct as an algebra homomorphism.
* `ConnesKreimer.MarkerCoherent`: `τ` gives a cut trunk the same marker as the tree it was cut
  from.

## Main results

* `ConnesKreimer.doubleCutsCrown_markerCuts`: for a coherent `τ`, nested marker cuts can be taken
  in either order.
* `ConnesKreimer.markerComulAlgHom_coassoc`: the marker coproduct is coassociative for a coherent
  `τ`.
* `ConnesKreimer.instIsBialgebraCutsMarkerCuts`: the marker cuts are an admissible policy, which
  gives `WithCuts R (markerCuts τ)` its `Bialgebra` instance.

## Implementation notes

The bialgebra laws are those of the generic coproduct of `Coproduct/WithCuts.lean`. Its
coassociativity asks that the two enumerations of nested cuts agree, which
`Core/Combinatorics/RootedTree/DoubleCut.lean` proves for every coherent extraction policy; the
marker policy is coherent exactly under marker coherence (`extractCoherent_leaveMarker`).

## References

* [marcolli-chomsky-berwick-2025]
* [foissy-2021]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### the marker coproduct on trees and forests

These instantiate the admissible-cut coproduct of `Coproduct/WithCuts.lean` at the enumeration
`markerCuts τ`. -/

/-- `markerComulAlgHom τ` is the marker coproduct on `ConnesKreimer R (UnorderedTree (α ⊕ β))`, an
algebra homomorphism, for the marker function `τ`. -/
noncomputable def markerComulAlgHom (τ : UnorderedTree (α ⊕ β) → β) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  comulOfCuts (markerCuts τ)

@[simp] theorem markerComulAlgHom_apply_of' (τ : UnorderedTree (α ⊕ β) → β)
    (F : Forest (UnorderedTree (α ⊕ β))) :
    markerComulAlgHom (R := R) τ (ConnesKreimer.of' F) = comulForestOfCuts (markerCuts τ) F :=
  comulOfCuts_apply_of' _ F

@[simp] theorem markerComulAlgHom_apply_ofTree (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    markerComulAlgHom (R := R) τ (ConnesKreimer.ofTree T) = comulTreeOfCuts (markerCuts τ) T :=
  comulOfCuts_apply_ofTree _ T

/-! ### Marker coherence

Coassociativity of the marker coproduct depends on the marker function. Iterating the coproduct
encodes a subtree that already carries markers, while the other cut order encodes the original
subtree; for `τ` the number of `inl` vertices the two disagree on a three-vertex chain of `inl`
vertices. `MarkerCoherent` states the hypothesis that coassociativity needs. -/

/-- A marker function `τ` is coherent when it gives a cut trunk, with its markers, the same
marker as the tree it was cut from. Constant functions are coherent (`markerCoherent_const`). -/
def MarkerCoherent (τ : UnorderedTree (α ⊕ β) → β) : Prop :=
  ∀ T : UnorderedTree (α ⊕ β), ∀ p ∈ markerCuts τ T, τ p.2 = τ T

/-- Constant marker functions are coherent. -/
theorem markerCoherent_const (b : β) :
    MarkerCoherent (fun _ : UnorderedTree (α ⊕ β) => b) :=
  fun _ _ _ => rfl

/-! ### The bialgebra

Under marker coherence nested marker cuts can be taken in either order, which is the combinatorial
core of coassociativity, and the empty cut is the only marker cut with
an empty crown (`markerCuts_filter_empty`). -/

/-- Under marker coherence the double marker cuts through the crown are those through the trunk. -/
theorem doubleCutsCrown_markerCuts {τ : UnorderedTree (α ⊕ β) → β} (hτ : MarkerCoherent τ)
    (T : UnorderedTree (α ⊕ β)) :
    doubleCutsCrown (markerCuts τ) T = doubleCutsTrunk (markerCuts τ) T :=
  doubleCutsCrown_eq_doubleCutsTrunk _ (markerCuts_mk τ)
    (extractCoherent_leaveMarker fun t p hp ↦
      hτ (.mk t) (projCut p) (Multiset.mem_map.mpr ⟨p, hp, rfl⟩)) T

/-- the marker coproduct is coassociative for a coherent marker function. -/
theorem markerComulAlgHom_coassoc {τ : UnorderedTree (α ⊕ β) → β} (hτ : MarkerCoherent τ) :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree (α ⊕ β))) _ _).toAlgHom.comp
        ((Algebra.TensorProduct.map (markerComulAlgHom (R := R) τ) (.id R _)).comp
          (markerComulAlgHom τ)) =
      (Algebra.TensorProduct.map (.id R _) (markerComulAlgHom (R := R) τ)).comp
        (markerComulAlgHom τ) :=
  comulOfCuts_coassoc (doubleCutsCrown_markerCuts hτ)

/-- For a coherent marker function, `markerCuts τ` is an admissible cut policy, so
`WithCuts R (markerCuts τ)` is a bialgebra.
Coherence enters through `Fact`, since instance search cannot find the hypothesis otherwise. -/
instance instIsBialgebraCutsMarkerCuts (τ : UnorderedTree (α ⊕ β) → β) [Fact (MarkerCoherent τ)] :
    IsBialgebraCuts (markerCuts τ) where
  doubleCutsCrown_eq := doubleCutsCrown_markerCuts Fact.out
  filter_card_eq_zero := markerCuts_filter_empty τ

/-- A coherent marker function gives the bialgebra of the marker coproduct by instance search. -/
noncomputable example (τ : UnorderedTree (α ⊕ β) → β) (hτ : MarkerCoherent τ) :
    Bialgebra R (WithCuts R (markerCuts τ)) :=
  haveI : Fact (MarkerCoherent τ) := ⟨hτ⟩
  inferInstance

end ConnesKreimer
