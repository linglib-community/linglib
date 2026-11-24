/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Finite
public import Linglib.Core.Combinatorics.Digraph.Reachable
public import Linglib.Core.Combinatorics.Digraph.Maps
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.Fin.Basic

/-!
# Digraphs on the positions of a sentence

A relation between the words of a sentence, such as that of a head to its dependents, is a
digraph on the positions of the sentence. The positions of a sentence of `n` words are `Fin n`,
in the order of the words.

This file builds digraphs from lists of arcs, reads a digraph in another order of its positions,
and defines a position together with its out-neighbours.

## Main definitions

* `Digraph.ofArcs`: the digraph with the listed arcs.
* `Digraph.linearize`, `Digraph.mirror`: a digraph read in another order of its positions, and
  from the last position to the first.
* `Digraph.localSubtree`: a position together with its out-neighbours.

## Implementation notes

A digraph carries no words: the words of a sentence are a function on its positions, held beside
the digraph by whatever reads them.
-/

@[expose] public section

/-! ### Digraphs from arcs, and their linearizations -/

namespace Digraph

variable {V : Type*} {n : ℕ}

/-- The digraph whose arcs are the listed pairs, each of a head and one of its dependents. -/
def ofArcs [DecidableEq V] (arcs : List (V × V)) : Digraph V where
  Adj v w := (v, w) ∈ arcs

@[simp] theorem ofArcs_adj [DecidableEq V] {arcs : List (V × V)} {v w : V} :
    (ofArcs arcs).Adj v w ↔ (v, w) ∈ arcs := Iff.rfl

instance [DecidableEq V] (arcs : List (V × V)) : DecidableRel (ofArcs arcs).Adj :=
  fun v w ↦ inferInstanceAs (Decidable ((v, w) ∈ arcs))

/-- The permutation of the positions given by a listing of them in a new order, sending the new
position `p` to the old position `order[p]`. -/
def orderPerm (order : List (Fin n)) (h : order.Perm (List.finRange n)) : Equiv.Perm (Fin n) :=
  (finCongr (h.length_eq.trans List.length_finRange).symm).trans
    ((h.nodup_iff.mpr (List.nodup_finRange n)).getEquivOfForallMemList order
      fun x ↦ h.mem_iff.mpr (List.mem_finRange x))

/-- The digraph read in the order `order`, which lists every position once. The word at position `p`
is the word of `G` at `order[p]`, and the arcs follow the words. -/
def linearize (G : Digraph (Fin n)) (order : List (Fin n)) (h : order.Perm (List.finRange n)) :
    Digraph (Fin n) :=
  G.comap (orderPerm order h)

instance (G : Digraph (Fin n)) [DecidableRel G.Adj] (order : List (Fin n))
    (h : order.Perm (List.finRange n)) : DecidableRel (G.linearize order h).Adj :=
  inferInstanceAs (DecidableRel (G.comap _).Adj)

/-- The mirror image of a digraph on positions, read from the last word to the first. -/
def mirror (G : Digraph (Fin n)) : Digraph (Fin n) := G.comap Fin.rev

@[simp] theorem mirror_adj (G : Digraph (Fin n)) (v w : Fin n) :
    G.mirror.Adj v w ↔ G.Adj v.rev w.rev := Iff.rfl

instance (G : Digraph (Fin n)) [DecidableRel G.Adj] : DecidableRel G.mirror.Adj :=
  inferInstanceAs (DecidableRel (G.comap _).Adj)

@[simp] theorem mirror_mirror (G : Digraph (Fin n)) : G.mirror.mirror = G :=
  Digraph.ext (by ext; simp)

theorem mirror_involutive : Function.Involutive (mirror (n := n)) := mirror_mirror

end Digraph

/-! ### Local subtrees -/

section LocalSubtree

open Finset

variable {n : ℕ}

/-- The *local subtree* of `v` is `v` together with its dependents. -/
def Digraph.localSubtree (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Finset (Fin n) :=
  insert v (G.outNeighborFinset v)

@[simp] theorem Digraph.self_mem_localSubtree (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : v ∈ G.localSubtree v :=
  mem_insert_self _ _

theorem Digraph.mem_localSubtree_iff {G : Digraph (Fin n)} [DecidableRel G.Adj] {v w : Fin n} :
    w ∈ G.localSubtree v ↔ w = v ∨ G.Adj v w := by
  simp [Digraph.localSubtree]

theorem Digraph.mem_localSubtree_of_adj {G : Digraph (Fin n)} [DecidableRel G.Adj] {v w : Fin n}
    (h : G.Adj v w) : w ∈ G.localSubtree v :=
  Digraph.mem_localSubtree_iff.2 (.inr h)

theorem Digraph.coe_localSubtree_subset_reachSet (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : (G.localSubtree v : Set (Fin n)) ⊆ G.reachSet v := fun w hw ↦ by
  rcases Digraph.mem_localSubtree_iff.1 (mem_coe.1 hw) with rfl | h
  exacts [.refl, .single h]

end LocalSubtree
