/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Size measures on unordered trees and their forests

## Main definitions

* `UnorderedTree.numEdges`: the edge count `numNodes - 1` of a rooted tree.

## Main results

* `UnorderedTree.sum_map_numNodes`: Euler's relation `#V = b₀ + #E` for forests, with
  `Multiset.card` the component count.
* `UnorderedTree.countP_leaves_le_numEdges`: counted leaves are among the non-root vertices
  whenever some vertex is uncounted.
-/

@[expose] public section

namespace UnorderedTree

variable {α : Type*}

/-- The number of edges of a rooted tree, `numNodes - 1`: every vertex except the root
    has exactly one parent edge. -/
def numEdges (t : UnorderedTree α) : ℕ := t.numNodes - 1

@[simp] theorem numEdges_leaf (a : α) : (leaf a : UnorderedTree α).numEdges = 0 := rfl

theorem numEdges_eq_numNodes_sub_one (t : UnorderedTree α) : t.numEdges = t.numNodes - 1 := rfl

theorem numEdges_add_one (t : UnorderedTree α) : t.numEdges + 1 = t.numNodes :=
  Nat.succ_pred_eq_of_pos t.numNodes_pos

theorem numEdges_node (a : α) (F : Multiset (UnorderedTree α)) :
    (node a F).numEdges = (F.map numNodes).sum := by
  simp [numEdges]

theorem numEdges_node_pair (a : α) (l r : UnorderedTree α) :
    (node a {l, r}).numEdges = l.numEdges + r.numEdges + 2 := by
  rw [numEdges_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, ← numEdges_add_one]
  omega

theorem numNodes_node_pair (a : α) (l r : UnorderedTree α) :
    (node a {l, r}).numNodes = l.numNodes + r.numNodes + 1 := by
  rw [numNodes_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]

theorem countP_leaves_le_numEdges (p : α → Prop) [DecidablePred p] (t : UnorderedTree α)
    (h : t.leaves.countP p < t.numNodes) : t.leaves.countP p ≤ t.numEdges :=
  Nat.le_sub_one_of_lt h

theorem sum_map_numNodes (F : Multiset (UnorderedTree α)) :
    (F.map numNodes).sum = Multiset.card F + (F.map numEdges).sum := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih, ← numEdges_add_one T]
    omega

end UnorderedTree
