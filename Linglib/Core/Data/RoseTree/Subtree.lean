/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Logic.Relation

/-!
# Subtrees of a rose tree

A tree `s` [is a subtree](##RoseTree.IsSubtree) of `t` when it is rooted at a node of `t`, reached
from `t` by descending through children. The relation is a partial order, since a proper subtree
[has fewer nodes](##RoseTree.IsSubtree.eq_of_numNodes_le), and
[`RoseTree.subtrees`](##RoseTree.subtrees) lists the subtrees of a tree in preorder, one per node,
which decides the relation. The subtrees are the trees found at the addresses of the tree, as
`RoseTree/Get.lean` shows.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

theorem numNodes_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.numNodes < t.numNodes := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [numNodes_node]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := numNodes) h)
    omega
/-- `IsSubtree s t` holds when `s` is the subtree of `t` rooted at one of its nodes, reached from
`t` by descending through children. -/
def IsSubtree (s t : RoseTree α) : Prop := Relation.ReflTransGen (fun c u ↦ c ∈ u.children) s t

@[refl]
theorem IsSubtree.refl (t : RoseTree α) : IsSubtree t t := Relation.ReflTransGen.refl

theorem IsSubtree.trans {r s t : RoseTree α} (h₁ : IsSubtree r s) (h₂ : IsSubtree s t) :
    IsSubtree r t :=
  Relation.ReflTransGen.trans h₁ h₂

theorem IsSubtree.of_mem_children {c t : RoseTree α} (h : c ∈ t.children) : IsSubtree c t :=
  Relation.ReflTransGen.single h

/-- Relabelling preserves the subtree relation. -/
theorem IsSubtree.map {β : Type*} {s t : RoseTree α} (f : α → β) (h : IsSubtree s t) :
    IsSubtree (s.map f) (t.map f) :=
  Relation.ReflTransGen.lift (RoseTree.map f) (fun c ⟨a, cs⟩ hc ↦ by
    simp only [Function.onFun, map_node, children_node]
    exact List.mem_map_of_mem hc) _ _ h

theorem isSubtree_node_iff {s : RoseTree α} {a : α} {cs : List (RoseTree α)} :
    IsSubtree s (node a cs) ↔ s = node a cs ∨ ∃ c ∈ cs, IsSubtree s c := by
  rw [IsSubtree, Relation.ReflTransGen.cases_tail_iff]
  simp only [children_node, eq_comm (a := node a cs)]
  exact or_congr_right ⟨fun ⟨c, h, hc⟩ ↦ ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, h, hc⟩⟩

@[simp] theorem isSubtree_leaf_iff {s : RoseTree α} {a : α} :
    IsSubtree s (leaf a) ↔ s = leaf a := by
  simp [isSubtree_node_iff]
theorem IsSubtree.numNodes_le {s t : RoseTree α} (h : IsSubtree s t) : s.numNodes ≤ t.numNodes := by
  induction h with
  | refl => exact le_rfl
  | tail _ hc ih => exact ih.trans (numNodes_lt_of_mem hc).le

theorem IsSubtree.eq_of_numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) (hn : t.numNodes ≤ s.numNodes) : s = t := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, hsc, hc⟩
  · rfl
  · exact absurd ((IsSubtree.numNodes_le hsc).trans_lt (numNodes_lt_of_mem hc)) (not_lt.2 hn)

theorem IsSubtree.antisymm {s t : RoseTree α}
    (h₁ : IsSubtree s t) (h₂ : IsSubtree t s) : s = t :=
  h₁.eq_of_numNodes_le h₂.numNodes_le

instance : IsPartialOrder (RoseTree α) IsSubtree where
  refl := .refl
  trans _ _ _ := .trans
  antisymm _ _ := IsSubtree.antisymm

mutual
/-- `subtrees t` lists the subtrees of `t` in preorder, `t` first, one per vertex. -/
def subtrees : RoseTree α → List (RoseTree α)
  | t@(node _ cs) => t :: subtreesList cs
/-- `subtreesList cs` lists the subtrees of the trees of `cs`. -/
def subtreesList : List (RoseTree α) → List (RoseTree α)
  | [] => []
  | c :: cs => subtrees c ++ subtreesList cs
end

theorem subtreesList_eq (cs : List (RoseTree α)) : subtreesList cs = cs.flatMap subtrees := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [subtreesList, ih, List.flatMap_cons]

@[simp] theorem subtrees_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).subtrees = node a cs :: cs.flatMap subtrees := by
  rw [subtrees, subtreesList_eq]

/-- The listed subtrees are exactly the subtrees. -/
theorem mem_subtrees {s t : RoseTree α} : s ∈ t.subtrees ↔ IsSubtree s t := by
  induction t with
  | node a cs ih =>
    rw [subtrees_node, List.mem_cons, List.mem_flatMap, isSubtree_node_iff]
    exact or_congr_right (exists_congr fun c ↦ and_congr_right fun hc ↦ ih c hc)

theorem self_mem_subtrees (t : RoseTree α) : t ∈ t.subtrees := mem_subtrees.mpr (.refl t)

theorem subtrees_map {β : Type*} (f : α → β) (t : RoseTree α) :
    (map f t).subtrees = t.subtrees.map (map f) := by
  induction t with
  | node a cs ih =>
    rw [map_node, subtrees_node, subtrees_node, List.map_cons, ← map_node, List.flatMap_map,
      List.map_flatMap]
    exact congrArg _ (List.flatMap_congr fun c hc ↦ ih c hc)

instance [DecidableEq α] (s t : RoseTree α) : Decidable (IsSubtree s t) :=
  decidable_of_iff _ mem_subtrees
end RoseTree
