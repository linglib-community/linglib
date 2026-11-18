/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Leaves
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# The leaves of an unordered tree

`RoseTree.leaves` is invariant under `RoseTree.Perm`, so it descends to the quotient as
`UnorderedTree.leaves`, the multiset of leaf labels. It has
[one element per leaf](##UnorderedTree.card_leaves), is natural in the labels
([`leaves_map`](##UnorderedTree.leaves_map)), and at a node with a child is the
[sum of the children's leaves](##UnorderedTree.leaves_node_cons).
-/

@[expose] public section

namespace UnorderedTree

variable {α β : Type*} (a : α)

/-- The multiset of leaf labels of an unordered tree. -/
def leaves : UnorderedTree α → Multiset α :=
  Quotient.lift RoseTree.leaves fun _ _ ↦ RoseTree.leaves_perm

@[simp] theorem leaves_mk (t : RoseTree α) : (mk t).leaves = t.leaves := rfl

@[simp] theorem leaves_leaf : (leaf a : UnorderedTree α).leaves = {a} := rfl

/-- The number of leaf labels is the number of leaves. -/
@[simp] theorem card_leaves (t : UnorderedTree α) : Multiset.card t.leaves = t.numLeaves :=
  Quotient.inductionOn t RoseTree.card_leaves

theorem leaves_ne_zero (t : UnorderedTree α) : t.leaves ≠ 0 :=
  Quotient.inductionOn t RoseTree.leaves_ne_zero

@[simp] theorem leaves_map (f : α → β) (t : UnorderedTree α) :
    (t.map f).leaves = t.leaves.map f :=
  Quotient.inductionOn t fun p ↦ by rw [quot_mk_eq_mk, map_mk, leaves_mk, RoseTree.leaves_map]; rfl

theorem numLeaves_le_numNodes (t : UnorderedTree α) : t.numLeaves ≤ t.numNodes :=
  Quotient.inductionOn t RoseTree.numLeaves_le_numNodes

theorem leaves_node_cons (T : UnorderedTree α) (cs : Multiset (UnorderedTree α)) :
    (node a (T ::ₘ cs)).leaves = T.leaves + (cs.map leaves).sum := by
  refine forest_inductionOn cs fun ps ↦ ?_
  refine Quotient.inductionOn T fun t ↦ ?_
  show (node a (Multiset.ofList ((t :: ps).map mk))).leaves
      = (mk t).leaves + ((Multiset.ofList (ps.map mk)).map leaves).sum
  rw [node_mk_tree_list, leaves_mk, RoseTree.leaves_node_cons]
  simp [List.map_map, Function.comp_def]

/-! ### Counting the leaves that satisfy a predicate -/

section CountP
variable (p : α → Prop) [DecidablePred p]

theorem countP_leaves_node_of_not (a : α) (F : Multiset (UnorderedTree α)) (h : ¬p a) :
    (node a F).leaves.countP p = (F.map fun T ↦ T.leaves.countP p).sum := by
  induction F using forest_inductionOn with
  | h cs =>
    rw [node_mk_tree_list, leaves_mk, RoseTree.countP_leaves_node_of_not p cs h,
      Multiset.map_coe, Multiset.sum_coe, List.map_map]
    rfl

/-- A root failing `p` is an uncounted vertex, so the counted leaves are fewer than the nodes. -/
theorem countP_leaves_lt_numNodes_of_not_root (t : UnorderedTree α) (h : ¬p t.value) :
    t.leaves.countP p < t.numNodes := by
  induction t using Quotient.inductionOn with
  | h t₀ => exact RoseTree.countP_leaves_lt_numNodes_of_not p h

end CountP

end UnorderedTree
