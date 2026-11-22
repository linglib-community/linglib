/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Maps between digraphs

This file defines the pullback `G.comap f` of a digraph along a function of vertices, in which
`a` is adjacent to `b` when `f a` is adjacent to `f b` in `G`, as `SimpleGraph.comap` does for
simple graphs.

## Implementation notes

Transport of a digraph along an equivalence `e` is written as the pullback along `e.symm`, so that
the adjacency of the transported digraph unfolds to the adjacency of the original and is decidable
by evaluation.
-/

@[expose] public section

namespace Digraph

variable {V W X : Type*}

/-- `G.comap f` is the digraph on `V` in which `a` is adjacent to `b` when `f a` is adjacent to
`f b` in `G`. -/
protected def comap (f : V → W) (G : Digraph W) : Digraph V where
  Adj a b := G.Adj (f a) (f b)

@[simp] theorem comap_adj {f : V → W} {G : Digraph W} {a b : V} :
    (G.comap f).Adj a b ↔ G.Adj (f a) (f b) := Iff.rfl

@[simp] theorem comap_id (G : Digraph V) : G.comap id = G := rfl

theorem comap_comap (f : V → W) (g : W → X) (G : Digraph X) :
    (G.comap g).comap f = G.comap (g ∘ f) := rfl

instance (f : V → W) (G : Digraph W) [DecidableRel G.Adj] : DecidableRel (G.comap f).Adj :=
  fun a b ↦ ‹DecidableRel G.Adj› (f a) (f b)

theorem comap_monotone (f : V → W) : Monotone (Digraph.comap f) := fun _ _ h _ _ hab ↦ h hab

instance [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] :
    DecidableRel G.toSimpleGraphInclusive.Adj :=
  fun a b ↦ inferInstanceAs (Decidable (a ≠ b ∧ (G.Adj a b ∨ G.Adj b a)))

/-- The undirected view of a pullback along an injection is the pullback of the undirected
view. -/
theorem toSimpleGraphInclusive_comap {f : V → W} (hf : Function.Injective f) (G : Digraph W) :
    (G.comap f).toSimpleGraphInclusive = G.toSimpleGraphInclusive.comap f := by
  ext a b
  simp [toSimpleGraphInclusive, hf.ne_iff]

end Digraph
