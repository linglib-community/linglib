/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Perm
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Algebra.Order.Monoid.Multiset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

/-!
# The leaves of a rose tree

`RoseTree.leaves` is the multiset of leaf labels of a rose tree, the frontier `RoseTree.leafList`
with its order forgotten. At a branching node it is the
[sum of the children's leaves](##RoseTree.leaves_node_of_ne_nil), so
[any additive map of it](##RoseTree.map_leaves_node_of_ne_nil) is computed child by child; it is
[invariant under `Perm`](##RoseTree.leaves_perm) and
[natural in the labels](##RoseTree.leaves_map). The frontier is a
[sublist of the preorder traversal](##RoseTree.leafList_sublist_values), so the leaves are among
the node labels and a statistic of the leaves is bounded by the same statistic of the nodes.

## Implementation notes

The frontier `leafList` is the one fold. `numLeaves` is its length and `leaves` its coercion to a
multiset, so the facts about either are read off the frontier and no second fold is related to it
by induction.
-/

@[expose] public section

namespace RoseTree

variable {α β : Type*}

/-! ### The frontier within the traversal -/

/-- The frontier is a sublist of the preorder traversal. -/
theorem leafList_sublist_values (t : RoseTree α) : t.leafList.Sublist t.values := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    rw [leafList_node_of_ne_nil a hcs, values_node]
    refine .cons a ?_
    clear hcs
    induction cs with
    | nil => exact .slnil
    | cons c cs ihcs =>
      exact (ih c List.mem_cons_self).append (ihcs fun d hd ↦ ih d (List.mem_cons_of_mem _ hd))

/-- A leaf is a vertex. -/
theorem numLeaves_le_numNodes (t : RoseTree α) : t.numLeaves ≤ t.numNodes := by
  rw [← length_leafList, ← length_values]
  exact t.leafList_sublist_values.length_le

/-! ### The multiset of leaves -/

/-- The multiset of leaf labels of a rose tree. -/
def leaves (t : RoseTree α) : Multiset α := t.leafList

/-- The leaf labels are the frontier with its order forgotten. -/
theorem coe_leafList (t : RoseTree α) : (t.leafList : Multiset α) = t.leaves := rfl

section Node
variable (a : α) (c : RoseTree α) (cs : List (RoseTree α))

@[simp] theorem leaves_leaf : leaves (node a []) = {a} := rfl

theorem leaves_node_of_ne_nil {cs : List (RoseTree α)} (h : cs ≠ []) :
    leaves (node a cs) = (cs.map leaves).sum := by
  rw [leaves, leafList_node_of_ne_nil a h, ← Multiset.coe_join, Multiset.join, Multiset.sum_coe,
    List.map_map]
  rfl

@[simp] theorem leaves_node_cons : leaves (node a (c :: cs)) = ((c :: cs).map leaves).sum :=
  leaves_node_of_ne_nil a (List.cons_ne_nil c cs)

/-- The children's leaves are among the leaves of a node, with equality unless it is a leaf. -/
theorem sum_map_leaves_le_node : (cs.map leaves).sum ≤ leaves (node a cs) := by
  rcases eq_or_ne cs [] with rfl | h
  · exact Multiset.zero_le _
  · exact (leaves_node_of_ne_nil a h).ge

theorem mem_leaves_node_of_ne_nil {cs : List (RoseTree α)} (h : cs ≠ []) {x : α} :
    x ∈ leaves (node a cs) ↔ ∃ c ∈ cs, x ∈ c.leaves := by
  rw [leaves_node_of_ne_nil a h, ← Multiset.sum_coe]
  exact Multiset.mem_join.trans (by simp)

end Node

theorem leaves_le_of_mem_children {c t : RoseTree α} (h : c ∈ t.children) :
    c.leaves ≤ t.leaves := by
  obtain ⟨a, cs⟩ := t
  exact (List.single_le_sum (fun _ _ ↦ Multiset.zero_le _) _ (List.mem_map_of_mem h)).trans
    (sum_map_leaves_le_node a cs)

theorem mem_leaves {t : RoseTree α} {x : α} : x ∈ t.leaves ↔ x ∈ t.leafList := Multiset.mem_coe

@[simp] theorem card_leaves (t : RoseTree α) : Multiset.card t.leaves = t.numLeaves := rfl

theorem leaves_ne_zero (t : RoseTree α) : t.leaves ≠ 0 := by
  rw [← coe_leafList, Ne, Multiset.coe_eq_zero]
  exact t.leafList_ne_nil

@[simp] theorem leaves_map (f : α → β) (t : RoseTree α) : (t.map f).leaves = t.leaves.map f := by
  rw [← coe_leafList, leafList_map, ← coe_leafList, Multiset.map_coe]

/-- The leaves are among the node labels. -/
theorem leaves_le_values (t : RoseTree α) : t.leaves ≤ (t.values : Multiset α) := by
  rw [← coe_leafList]
  exact Multiset.coe_le.2 t.leafList_sublist_values.subperm

/-! ### `Perm` invariance -/

/-- Reordering children does not change the leaves. -/
theorem leaves_perm {t s : RoseTree α} (h : Perm t s) : t.leaves = s.leaves :=
  Multiset.coe_eq_coe.2 h.leafList_perm

/-! ### Additive maps of the leaves -/

section AddMonoidHom
variable {F M : Type*} [AddMonoid M] [FunLike F (Multiset α) M] [AddMonoidHomClass F (Multiset α) M]
  (φ : F) (a : α)

/-- An additive map of the leaves of a branching node is the sum of its values on the leaves of
the children. -/
theorem map_leaves_node_of_ne_nil {cs : List (RoseTree α)} (h : cs ≠ []) :
    φ (leaves (node a cs)) = (cs.map fun t ↦ φ t.leaves).sum := by
  rw [leaves_node_of_ne_nil a h, map_list_sum, List.map_map]
  rfl

theorem map_leaves_node_cons (c : RoseTree α) (cs : List (RoseTree α)) :
    φ (leaves (node a (c :: cs))) = ((c :: cs).map fun t ↦ φ t.leaves).sum :=
  map_leaves_node_of_ne_nil φ a (List.cons_ne_nil c cs)

/-- An additive map that vanishes on the label of the root does not tell a leaf from a branching
node. -/
theorem map_leaves_node_of_map_singleton_eq_zero (h : φ {a} = 0) (cs : List (RoseTree α)) :
    φ (leaves (node a cs)) = (cs.map fun t ↦ φ t.leaves).sum := by
  rcases eq_or_ne cs [] with rfl | hcs
  · exact h
  · exact map_leaves_node_of_ne_nil φ a hcs

end AddMonoidHom

/-! ### Counting the leaves that satisfy a predicate -/

section CountP
variable (p : α → Prop) [DecidablePred p]

@[simp] theorem countP_leaves_node_cons (a : α) (c : RoseTree α) (cs : List (RoseTree α)) :
    (leaves (node a (c :: cs))).countP p = ((c :: cs).map fun t ↦ t.leaves.countP p).sum :=
  map_leaves_node_cons (Multiset.countPAddMonoidHom p) a c cs

theorem countP_leaves_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    (leaves (node a cs)).countP p = (cs.map fun t ↦ t.leaves.countP p).sum :=
  map_leaves_node_of_ne_nil (Multiset.countPAddMonoidHom p) a h

theorem countP_leaves_node_of_not {a : α} (cs : List (RoseTree α)) (h : ¬p a) :
    (leaves (node a cs)).countP p = (cs.map fun t ↦ t.leaves.countP p).sum :=
  map_leaves_node_of_map_singleton_eq_zero (Multiset.countPAddMonoidHom p) a
    (by simpa [Multiset.countP_eq_zero] using h) cs

/-- A root failing `p` is an uncounted vertex, so the counted leaves are fewer than the nodes. -/
theorem countP_leaves_lt_numNodes_of_not {t : RoseTree α} (h : ¬p t.value) :
    t.leaves.countP p < t.numNodes := by
  obtain ⟨a, cs⟩ := t
  rw [value_node] at h
  calc (leaves (node a cs)).countP p
    _ ≤ ((node a cs).values : Multiset α).countP p :=
      Multiset.countP_le_of_le p (leaves_le_values _)
    _ = ((cs.map values).flatten : Multiset α).countP p := by
      rw [values_node, ← Multiset.cons_coe, Multiset.countP_cons_of_neg _ h]
    _ ≤ (cs.map values).flatten.length := Multiset.countP_le_card _ _
    _ < numNodes (node a cs) := by rw [← length_values, values_node]; exact Nat.lt_succ_self _

end CountP

end RoseTree
