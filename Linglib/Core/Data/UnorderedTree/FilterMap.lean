/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.FilterMap
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Partial label maps on unordered trees

`UnorderedTree.filterMap f` relabels an unordered tree along `f : α → Option β`, dropping every
subtree whose root `f` sends to `none`. It is the `UnorderedTree.fold` with the same algebra as
`RoseTree.filterMap`, read on multisets of children.

## Main definitions

* `UnorderedTree.filterMap`: the partial map.

## Main results

* `UnorderedTree.filterMap_node`: at a node, the surviving children are the `Multiset.filterMap`
  of the children.
* `UnorderedTree.filterMap_mk`: the map commutes with the projection from rose trees.
-/

@[expose] public section

namespace UnorderedTree

variable {α β : Type*}

/-- `filterMap f t` relabels `t` along `f`, dropping the subtrees whose root `f` sends to `none`.
It is `none` when the root itself is dropped. -/
def filterMap (f : α → Option β) : UnorderedTree α → Option (UnorderedTree β) :=
  fold fun a cs ↦ (f a).map fun b ↦ node b (cs.filterMap id)

@[simp] theorem filterMap_node (f : α → Option β) (a : α) (F : Multiset (UnorderedTree α)) :
    filterMap f (node a F) = (f a).map fun b ↦ node b (F.filterMap (filterMap f)) := by
  rw [filterMap, fold_node, Multiset.filterMap_map, Function.id_comp]

@[simp] theorem filterMap_mk (f : α → Option β) (t : RoseTree α) :
    filterMap f (mk t) = (t.filterMap f).map mk := by
  induction t with
  | node a cs ih =>
    rw [← node_mk_tree_list, filterMap_node, RoseTree.filterMap_node, Option.map_map,
      Multiset.filterMap_coe, List.filterMap_map, List.filterMap_congr (f := filterMap f ∘ mk) ih]
    refine congrArg (Option.map · (f a)) (funext fun b ↦ ?_)
    rw [Function.comp_apply, ← node_mk_tree_list, List.map_filterMap]

@[simp] theorem filterMap_getLeft?_map_inl (t : UnorderedTree α) :
    filterMap Sum.getLeft? (map (Sum.inl : α → α ⊕ β) t) = some t :=
  Quotient.inductionOn t fun t ↦ by
    rw [quot_mk_eq_mk, map_mk, filterMap_mk, RoseTree.filterMap_getLeft?_map_inl, Option.map_some]

end UnorderedTree
