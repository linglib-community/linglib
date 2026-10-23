/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Leaves
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Leaf projections of an unordered tree

`RoseTree.leavesWithDepth` and `RoseTree.leaves` are `Perm`-invariant, so they descend to the
quotient, and the leaf statistics by predicate descend with them.

## Main definitions

* `UnorderedTree.leavesWithDepth`, `UnorderedTree.leaves`: the projections.

## Main results

* `UnorderedTree.card_leaves`: the projection has `numLeaves` elements.
* `UnorderedTree.countP_leaves_lt_numNodes_of_not_root`: when the root fails the predicate,
  the counted leaves are among the non-root vertices.
-/

@[expose] public section

namespace UnorderedTree

variable {α : Type*} (a : α)

/-- The leaves of an unordered tree, each paired with its distance from the root. -/
def leavesWithDepth : UnorderedTree α → Multiset (α × ℕ) :=
  Quotient.lift RoseTree.leavesWithDepth fun _ _ => RoseTree.leavesWithDepth_perm

@[simp] theorem leavesWithDepth_mk (t : RoseTree α) :
    (mk t).leavesWithDepth = t.leavesWithDepth := rfl

/-- The multiset of leaf labels of an unordered tree. -/
def leaves (t : UnorderedTree α) : Multiset α := t.leavesWithDepth.map Prod.fst

@[simp] theorem leaves_mk (t : RoseTree α) : (mk t).leaves = t.leaves := rfl

@[simp] theorem leavesWithDepth_leaf :
    (leaf a : UnorderedTree α).leavesWithDepth = {(a, 0)} := rfl

@[simp] theorem leaves_leaf : (leaf a : UnorderedTree α).leaves = {a} := rfl

theorem card_leavesWithDepth (t : UnorderedTree α) :
    Multiset.card t.leavesWithDepth = t.numLeaves :=
  Quotient.inductionOn t fun p => RoseTree.card_leavesWithDepth p

/-- The number of leaf labels is the number of leaves. -/
theorem card_leaves (t : UnorderedTree α) : Multiset.card t.leaves = t.numLeaves := by
  rw [leaves, Multiset.card_map, card_leavesWithDepth]

theorem numLeaves_le_numNodes (t : UnorderedTree α) : t.numLeaves ≤ t.numNodes :=
  Quotient.inductionOn t fun p => RoseTree.numLeaves_le_numNodes p

theorem leaves_node_cons (T : UnorderedTree α) (cs : Multiset (UnorderedTree α)) :
    (node a (T ::ₘ cs)).leaves = T.leaves + (cs.map leaves).sum := by
  refine forest_inductionOn cs fun ps => ?_
  refine Quotient.inductionOn T fun t => ?_
  show (node a (Multiset.ofList ((t :: ps).map mk))).leaves
      = (mk t).leaves + ((Multiset.ofList (ps.map mk)).map leaves).sum
  rw [node_mk_tree_list, leaves_mk, RoseTree.leaves_node_cons]
  simp [List.map_map, Function.comp_def]

/-! ### Leaf statistics by predicate -/

section Statistics
variable (p : α → Prop) [DecidablePred p]

theorem countP_leaves_leaf (a : α) :
    (leaf a : UnorderedTree α).leaves.countP p = if p a then 1 else 0 :=
  RoseTree.countP_leaves_leaf p a

theorem countP_leaves_node_of_not (a : α) (F : Multiset (UnorderedTree α)) (h : ¬p a) :
    (node a F).leaves.countP p = (F.map fun T => T.leaves.countP p).sum := by
  induction F using forest_inductionOn with
  | h cs =>
    rw [node_mk_tree_list, leaves_mk, RoseTree.countP_leaves_node_of_not p cs h,
      Multiset.map_coe, Multiset.sum_coe, List.map_map]
    rfl

/-- A root failing `p` is an uncounted vertex, so the count is strict. -/
theorem countP_leaves_lt_numNodes_of_not_root (t : UnorderedTree α) (h : ¬p t.value) :
    t.leaves.countP p < t.numNodes := by
  induction t using Quotient.inductionOn with
  | h t₀ =>
    cases t₀ with
    | node x cs => exact RoseTree.countP_leaves_lt_numNodes_of_not p cs h

end Statistics

end UnorderedTree
