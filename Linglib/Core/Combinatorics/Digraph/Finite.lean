/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite neighbourhoods and arcs of a digraph

For a digraph with decidable adjacency on a finite vertex type, this file defines the finite sets
of out-neighbours and of in-neighbours of a vertex and the finite set of arcs, as
`SimpleGraph.neighborFinset` and `SimpleGraph.edgeFinset` do for a simple graph.

## Main definitions

* `Digraph.outNeighborFinset`, `Digraph.inNeighborFinset`: the vertices a vertex has an arc to,
  and those that have an arc to it.
* `Digraph.arcs`: the arcs, each a pair of a vertex and one of its out-neighbours.
-/

@[expose] public section

namespace Digraph

variable {V : Type*} {G : Digraph V} {v w : V}

section Finite

variable [Fintype V] (G) [DecidableRel G.Adj]

/-- The out-neighbours of `v`. -/
def outNeighborFinset (v : V) : Finset V := {w | G.Adj v w}

/-- The in-neighbours of `w`. -/
def inNeighborFinset (w : V) : Finset V := {v | G.Adj v w}

/-- The arcs of a digraph, each a pair of a vertex and one of its out-neighbours. -/
def arcs : Finset (V × V) := {p | G.Adj p.1 p.2}

variable {G}

@[simp] theorem mem_outNeighborFinset : w ∈ G.outNeighborFinset v ↔ G.Adj v w := by
  simp [outNeighborFinset]

@[simp] theorem mem_inNeighborFinset : v ∈ G.inNeighborFinset w ↔ G.Adj v w := by
  simp [inNeighborFinset]

@[simp] theorem mem_arcs {p : V × V} : p ∈ G.arcs ↔ G.Adj p.1 p.2 := by simp [arcs]

theorem card_arcs : G.arcs.card = ∑ v, (G.outNeighborFinset v).card := by
  simp only [arcs, outNeighborFinset, Finset.card_filter, Fintype.sum_prod_type]

end Finite

end Digraph
