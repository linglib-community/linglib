/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Pruning a tree to the vertices above a marked vertex

`prune p t` keeps the vertices of `t` that have a vertex satisfying `p` at or below them, and is
`none` when no vertex of `t` satisfies `p`. Where `filterMap` removes what lies below a dropped
vertex, `prune` removes what lies above no kept one. A tree
[whose leaves all satisfy `p`](##UnorderedTree.prune_eq_some_self) is left as it is. Followed by
the contraction of unary vertices, pruning to a set of leaves is the restriction of a rooted tree
to those leaves.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-- `prune p t` keeps the vertices of `t` with a vertex satisfying `p` at or below them. It is
`none` when no vertex of `t` satisfies `p`. -/
def prune : RoseTree α → Option (RoseTree α) :=
  fold fun a cs ↦ if p a ∨ cs.filterMap id ≠ [] then some (node a (cs.filterMap id)) else none

@[simp] theorem prune_node (a : α) (cs : List (RoseTree α)) :
    prune p (node a cs) = if p a ∨ cs.filterMap (prune p) ≠ [] then
      some (node a (cs.filterMap (prune p))) else none := by
  rw [prune, fold_node, List.filterMap_map, Function.id_comp]

end RoseTree

namespace UnorderedTree

variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-- `prune p t` keeps the vertices of `t` with a vertex satisfying `p` at or below them. It is
`none` when no vertex of `t` satisfies `p`. -/
def prune : UnorderedTree α → Option (UnorderedTree α) :=
  fold fun a F ↦
    if p a ∨ (F.filterMap id).card ≠ 0 then some (node a (F.filterMap id)) else none

@[simp] theorem prune_node (a : α) (F : Multiset (UnorderedTree α)) :
    prune p (node a F) = if p a ∨ (F.filterMap (prune p)).card ≠ 0 then
      some (node a (F.filterMap (prune p))) else none := by
  rw [prune, fold_node, Multiset.filterMap_map, Function.id_comp]

theorem prune_leaf (a : α) : prune p (leaf a) = if p a then some (leaf a) else none := by
  rw [← node_zero, prune_node]
  simp

@[simp] theorem prune_mk (t : RoseTree α) : prune p (mk t) = (t.prune p).map mk :=
  (RoseTree.fold_hom (Option.map mk) (fun a cs ↦ by
    have h : (Multiset.ofList (cs.map (Option.map mk))).filterMap id =
        Multiset.ofList ((cs.filterMap id).map mk) := by
      rw [Multiset.filterMap_coe, List.filterMap_map, List.map_filterMap]; rfl
    by_cases hp : p a ∨ cs.filterMap id ≠ []
    · rw [ite_eq_left hp, Option.map_some, ← node_mk_tree_list, ← h]
      exact (ite_eq_left (hp.imp_right fun hc ↦ by simpa [h] using hc)).symm
    · rw [ite_eq_right hp, Option.map_none]
      exact (ite_eq_right fun h' ↦ hp (h'.imp_right fun hc ↦ by simpa [h] using hc)).symm) t).symm

/-- A tree whose leaves all satisfy `p` is its own pruning. -/
theorem prune_eq_some_self {t : UnorderedTree α} (h : ∀ a ∈ t.leaves, p a) :
    prune p t = some t := by
  induction t with
  | node a F ih =>
    induction F using Multiset.induction with
    | empty => rw [node_zero, prune_leaf, ite_eq_left (h a (by simp))]
    | cons c F _ =>
      have hc : ∀ d ∈ c ::ₘ F, prune p d = some d := fun d hd ↦ ih d hd fun b hb ↦ h b <| by
        obtain ⟨G, hG⟩ := Multiset.exists_cons_of_mem hd
        rw [hG, leaves_node_cons]
        exact Multiset.mem_add.2 (.inl hb)
      have hF : (c ::ₘ F).filterMap (prune p) = c ::ₘ F := by
        rw [← Function.id_comp (prune p), ← Multiset.filterMap_map, Multiset.map_congr rfl hc,
          Multiset.filterMap_map, Function.id_comp, Multiset.filterMap_some]
      rw [prune_node, hF, ite_eq_left (.inr (by simp))]

end UnorderedTree
