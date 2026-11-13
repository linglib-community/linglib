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
subtree whose root `f` sends to `none`. It is the `UnorderedTree.fold` with the algebra of
`RoseTree.filterMap` read on multisets of children, so at a node the surviving children are
[the `Multiset.filterMap` of the children](##UnorderedTree.filterMap_node), and it
[commutes with the projection from rose trees](##UnorderedTree.filterMap_mk). The equations of
`RoseTree.filterMap` descend along the projection, among them
[the preservation of Kleisli composition](##UnorderedTree.filterMap_filterMap).
-/

@[expose] public section

namespace UnorderedTree

variable {α β γ : Type*}

/-- `filterMap f t` relabels `t` along `f`, dropping the subtrees whose root `f` sends to `none`.
It is `none` when the root itself is dropped. -/
def filterMap (f : α → Option β) : UnorderedTree α → Option (UnorderedTree β) :=
  fold fun a cs ↦ (f a).map fun b ↦ node b (cs.filterMap id)

@[simp] theorem filterMap_node (f : α → Option β) (a : α) (F : Multiset (UnorderedTree α)) :
    filterMap f (node a F) = (f a).map fun b ↦ node b (F.filterMap (filterMap f)) := by
  rw [filterMap, fold_node, Multiset.filterMap_map, Function.id_comp]

@[simp] theorem filterMap_mk (f : α → Option β) (t : RoseTree α) :
    filterMap f (mk t) = (t.filterMap f).map mk :=
  (RoseTree.fold_hom (Option.map mk) (fun a cs ↦ by
    refine (Option.map_map ..).trans (congrArg (Option.map · (f a)) (funext fun b ↦ ?_))
    rw [Function.comp_apply, ← node_mk_tree_list, List.map_filterMap, Multiset.filterMap_coe,
      List.filterMap_map]
    rfl) t).symm

/-- The root of the result is the image of the root. -/
@[simp] theorem map_value_filterMap (f : α → Option β) (t : UnorderedTree α) :
    (filterMap f t).map value = f t.value :=
  Quotient.inductionOn t fun t ↦ by
    rw [quot_mk_eq_mk, filterMap_mk, Option.map_map]
    exact RoseTree.map_value_filterMap f t

theorem filterMap_eq_none_iff {f : α → Option β} {t : UnorderedTree α} :
    filterMap f t = none ↔ f t.value = none := by
  rw [← map_value_filterMap f t, Option.map_eq_none_iff]

/-! ### Composition -/

/-- `filterMap` preserves the Kleisli composition of partial maps. -/
theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (t : UnorderedTree α) :
    (filterMap f t).bind (filterMap g) = filterMap (fun a ↦ (f a).bind g) t :=
  Quotient.inductionOn t fun t ↦ by
    rw [quot_mk_eq_mk, filterMap_mk, filterMap_mk, ← RoseTree.filterMap_filterMap,
      Option.bind_map, Option.map_bind]
    exact congrArg _ (funext fun s ↦ filterMap_mk g s)

/-- A total map drops nothing. -/
theorem filterMap_some_comp (g : α → β) : filterMap (some ∘ g) = some ∘ map g :=
  funext fun t ↦ Quotient.inductionOn t fun t ↦ by
    rw [quot_mk_eq_mk, filterMap_mk, RoseTree.filterMap_some_comp]
    rfl

@[simp] theorem filterMap_some (t : UnorderedTree α) : filterMap some t = some t := by
  rw [← Function.comp_id some, filterMap_some_comp, Function.comp_apply, map_id]

theorem filterMap_map (f : β → Option γ) (g : α → β) (t : UnorderedTree α) :
    filterMap f (map g t) = filterMap (f ∘ g) t := by
  rw [← Option.bind_some (f := filterMap f), ← Function.comp_apply (f := some),
    ← filterMap_some_comp, filterMap_filterMap]
  rfl

theorem map_filterMap (f : α → Option β) (g : β → γ) (t : UnorderedTree α) :
    (filterMap f t).map (map g) = filterMap (fun a ↦ (f a).map g) t := by
  rw [Option.map_eq_bind, ← filterMap_some_comp, filterMap_filterMap]
  exact congrArg (filterMap · t) (funext fun _ ↦ Option.map_eq_bind.symm)

@[simp] theorem filterMap_getLeft?_map_inl (t : UnorderedTree α) :
    filterMap Sum.getLeft? (map (Sum.inl : α → α ⊕ β) t) = some t := by
  rw [filterMap_map]
  exact filterMap_some t

end UnorderedTree
