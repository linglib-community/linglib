/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Basic

/-!
# Partial label maps on rose trees

`RoseTree.filterMap f` relabels a rose tree along `f : α → Option β`, dropping every subtree whose
root `f` sends to `none`. The result is `none` exactly when the root itself is dropped. It is the
counterpart on rose trees of `List.filterMap`, and a `RoseTree.fold`.

## Main definitions

* `RoseTree.filterMap`: the partial map.

## Main results

* `RoseTree.filterMap_node`: at a node, the surviving children are the `List.filterMap` of the
  children.
* `RoseTree.filterMap_map`: `filterMap f (map g t) = filterMap (f ∘ g) t`.
* `RoseTree.filterMap_some`: a total map drops nothing.
-/

@[expose] public section

namespace RoseTree

variable {α β γ : Type*}

/-- `filterMap f t` relabels `t` along `f`, dropping the subtrees whose root `f` sends to `none`.
It is `none` when the root itself is dropped. -/
def filterMap (f : α → Option β) : RoseTree α → Option (RoseTree β) :=
  fold fun a cs ↦ (f a).map fun b ↦ node b (cs.filterMap id)

@[simp] theorem filterMap_node (f : α → Option β) (a : α) (cs : List (RoseTree α)) :
    filterMap f (node a cs) = (f a).map fun b ↦ node b (cs.filterMap (filterMap f)) := by
  rw [filterMap, fold_node, List.filterMap_map, Function.id_comp]

/-! ### Composition with total maps -/

theorem filterMap_map (f : β → Option γ) (g : α → β) (t : RoseTree α) :
    filterMap f (map g t) = filterMap (f ∘ g) t := by
  induction t with
  | node a cs ih =>
    rw [map_node, filterMap_node, filterMap_node, List.filterMap_map,
      List.filterMap_congr (f := filterMap f ∘ map g) ih, Function.comp_apply]

/-- A total map drops nothing. -/
theorem filterMap_some (g : α → β) (t : RoseTree α) :
    filterMap (fun a ↦ some (g a)) t = some (map g t) := by
  induction t with
  | node a cs ih =>
    rw [filterMap_node, map_node, Option.map_some, List.filterMap_congr ih,
      List.filterMap_eq_map']

@[simp] theorem filterMap_getLeft?_map_inl (t : RoseTree α) :
    filterMap Sum.getLeft? (map (Sum.inl : α → α ⊕ β) t) = some t := by
  rw [filterMap_map,
    show (Sum.getLeft? ∘ (Sum.inl : α → α ⊕ β)) = (fun a ↦ some (id a)) from rfl,
    filterMap_some, id_map]

end RoseTree
