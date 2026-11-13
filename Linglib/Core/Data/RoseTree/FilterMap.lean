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
root `f` sends to `none`; it is the counterpart on rose trees of `List.filterMap`, and a
`RoseTree.fold`. The root of the result is [the image of the root](##RoseTree.map_value_filterMap),
so the result is `none` exactly when the root is dropped. Partial label maps compose as partial
tree maps: [`filterMap` preserves Kleisli composition](##RoseTree.filterMap_filterMap) and
[sends a total map to `map`](##RoseTree.filterMap_some_comp), and the equations for a `map` before
or after a `filterMap` are cases of these two.
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

/-- The root of the result is the image of the root. -/
@[simp] theorem map_value_filterMap (f : α → Option β) (t : RoseTree α) :
    (filterMap f t).map value = f t.value := by
  cases t with
  | node a cs => rw [filterMap_node, Option.map_map]; exact Option.map_id'

theorem filterMap_eq_none_iff {f : α → Option β} {t : RoseTree α} :
    filterMap f t = none ↔ f t.value = none := by
  rw [← map_value_filterMap f t, Option.map_eq_none_iff]

/-! ### Composition -/

/-- `filterMap` preserves the Kleisli composition of partial maps. -/
theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (t : RoseTree α) :
    (filterMap f t).bind (filterMap g) = filterMap (fun a ↦ (f a).bind g) t := by
  induction t with
  | node a cs ih =>
    rw [filterMap_node, filterMap_node, ← List.filterMap_congr ih, ← List.filterMap_filterMap]
    cases f a with
    | none => rfl
    | some b => rw [Option.map_some, Option.bind_some, Option.bind_some, filterMap_node]

/-- A total map drops nothing. -/
theorem filterMap_some_comp (g : α → β) : filterMap (some ∘ g) = some ∘ map g :=
  funext fun t ↦ by
    induction t with
    | node a cs ih =>
      rw [filterMap_node, Function.comp_apply, Function.comp_apply, map_node, Option.map_some,
        List.filterMap_congr ih, List.filterMap_eq_map]

@[simp] theorem filterMap_some (t : RoseTree α) : filterMap some t = some t := by
  rw [← Function.comp_id some, filterMap_some_comp, Function.comp_apply, map_id]

theorem filterMap_map (f : β → Option γ) (g : α → β) (t : RoseTree α) :
    filterMap f (map g t) = filterMap (f ∘ g) t := by
  rw [← Option.bind_some (f := filterMap f), ← Function.comp_apply (f := some),
    ← filterMap_some_comp, filterMap_filterMap]
  rfl

theorem map_filterMap (f : α → Option β) (g : β → γ) (t : RoseTree α) :
    (filterMap f t).map (map g) = filterMap (fun a ↦ (f a).map g) t := by
  rw [Option.map_eq_bind, ← filterMap_some_comp, filterMap_filterMap]
  exact congrArg (filterMap · t) (funext fun _ ↦ Option.map_eq_bind.symm)

@[simp] theorem filterMap_getLeft?_map_inl (t : RoseTree α) :
    filterMap Sum.getLeft? (map (Sum.inl : α → α ⊕ β) t) = some t := by
  rw [filterMap_map]
  exact filterMap_some t

end RoseTree
