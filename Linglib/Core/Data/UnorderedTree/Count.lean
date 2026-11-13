/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Edges of an unordered tree

Every vertex of a rooted tree except the root has exactly one parent edge, so the edge count
`UnorderedTree.numEdges` is [one less than the vertex count](##UnorderedTree.numEdges_add_one).
A child of a node contributes its own edges and the edge that attaches it, which is the
[recursion at a node](##UnorderedTree.numEdges_node). Summed over a forest, the same count is
[Euler's relation](##UnorderedTree.sum_map_numNodes): the vertices are the components plus the
edges.
-/

@[expose] public section

namespace UnorderedTree

variable {α β : Type*}

/-- The number of edges of a rooted tree, `numNodes - 1`: every vertex except the root
    has exactly one parent edge. -/
def numEdges (t : UnorderedTree α) : ℕ := t.numNodes - 1

@[simp] theorem numEdges_leaf (a : α) : (leaf a : UnorderedTree α).numEdges = 0 := rfl

theorem numEdges_add_one (t : UnorderedTree α) : t.numEdges + 1 = t.numNodes :=
  Nat.succ_pred_eq_of_pos t.numNodes_pos

/-- A number is below the vertex count exactly when it is at most the edge count. -/
theorem lt_numNodes_iff {t : UnorderedTree α} {n : ℕ} : n < t.numNodes ↔ n ≤ t.numEdges := by
  rw [← numEdges_add_one, Nat.lt_succ_iff]

@[simp] theorem numEdges_map (f : α → β) (t : UnorderedTree α) :
    (t.map f).numEdges = t.numEdges :=
  congrArg (· - 1) (numNodes_map f t)

/-- Euler's relation for forests: the vertices are the components, counted by `Multiset.card`,
    plus the edges. -/
theorem sum_map_numNodes (F : Multiset (UnorderedTree α)) :
    (F.map numNodes).sum = Multiset.card F + (F.map numEdges).sum := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih, ← numEdges_add_one T]
    omega

/-- Each child contributes its own edges and the edge that attaches it to the root. -/
theorem numEdges_node (a : α) (F : Multiset (UnorderedTree α)) :
    (node a F).numEdges = Multiset.card F + (F.map numEdges).sum := by
  rw [numEdges, numNodes_node, Nat.add_sub_cancel, sum_map_numNodes]

theorem numEdges_node_pair (a : α) (l r : UnorderedTree α) :
    (node a {l, r}).numEdges = l.numEdges + r.numEdges + 2 := by
  rw [numEdges_node, Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton,
    Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
  omega

end UnorderedTree
