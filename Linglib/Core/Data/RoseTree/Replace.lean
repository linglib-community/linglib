/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.Order.Group.Multiset
public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Core.Data.RoseTree.Leaves

/-!
# Substitution of subtrees of a rose tree

`RoseTree.replaceIf p r` replaces every outermost subtree satisfying `p` by `r`, and
`RoseTree.modifyIf p f` applies `f` to each. The subtrees replaced are `RoseTree.outerMatches p`,
the first match in preorder among them, and replacing them trades their leaves for copies of the
replacement's.

## Main definitions

* `RoseTree.replaceIf`, `RoseTree.modifyIf`, `RoseTree.outerMatches`

## Main results

* `RoseTree.mem_outerMatches_of_find?`: the first match in preorder is an outermost one.
* `RoseTree.leaves_replaceIf`: substitution trades the leaves of the replaced subtrees for those of
  the replacement.
* `RoseTree.filterMap_leaves_replaceIf_add`: replacing the copies of a subtree whose leaves occur
  once trades the leaves of one copy.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

section ReplaceIf

variable (p : RoseTree α → Prop) [DecidablePred p] (r : RoseTree α)

mutual
/-- Replace every subtree satisfying `p` by `r`, testing each subtree before its children. -/
def replaceIf : RoseTree α → RoseTree α
  | .node a cs => if p (.node a cs) then r else .node a (replaceIfList cs)
/-- `replaceIf` in each tree of a list. -/
def replaceIfList : List (RoseTree α) → List (RoseTree α)
  | [] => []
  | c :: cs => replaceIf c :: replaceIfList cs
end

theorem replaceIfList_eq (cs : List (RoseTree α)) :
    replaceIfList p r cs = cs.map (replaceIf p r) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [replaceIfList, ih, List.map_cons]

theorem replaceIf_node (a : α) (cs : List (RoseTree α)) :
    replaceIf p r (node a cs) = if p (node a cs) then r else node a (cs.map (replaceIf p r)) := by
  rw [replaceIf, replaceIfList_eq]

end ReplaceIf

section ModifyIf

variable (p : RoseTree α → Prop) [DecidablePred p] (f : RoseTree α → RoseTree α)

mutual
/-- Apply `f` to every outermost subtree satisfying `p`, testing each subtree before its children;
`replaceIf` is the case of a constant `f`. -/
def modifyIf : RoseTree α → RoseTree α
  | .node a cs => if p (.node a cs) then f (.node a cs) else .node a (modifyIfList cs)
/-- `modifyIf` in each tree of a list. -/
def modifyIfList : List (RoseTree α) → List (RoseTree α)
  | [] => []
  | c :: cs => modifyIf c :: modifyIfList cs
end

theorem modifyIfList_eq (cs : List (RoseTree α)) :
    modifyIfList p f cs = cs.map (modifyIf p f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [modifyIfList, ih, List.map_cons]

theorem modifyIf_node (a : α) (cs : List (RoseTree α)) :
    modifyIf p f (node a cs) = if p (node a cs) then f (node a cs) else
      node a (cs.map (modifyIf p f)) := by
  rw [modifyIf, modifyIfList_eq]

end ModifyIf

section OuterMatches

variable (p : RoseTree α → Prop) [DecidablePred p]

mutual
/-- The outermost subtrees satisfying `p`, in preorder: those `replaceIf p` replaces. -/
def outerMatches : RoseTree α → List (RoseTree α)
  | .node a cs => if p (.node a cs) then [.node a cs] else outerMatchesList cs
/-- `outerMatches` of the trees of a list. -/
def outerMatchesList : List (RoseTree α) → List (RoseTree α)
  | [] => []
  | c :: cs => outerMatches c ++ outerMatchesList cs
end

theorem outerMatchesList_eq (cs : List (RoseTree α)) :
    outerMatchesList p cs = cs.flatMap (outerMatches p) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [outerMatchesList, ih, List.flatMap_cons]

theorem outerMatches_node (a : α) (cs : List (RoseTree α)) :
    outerMatches p (node a cs) =
      if p (node a cs) then [node a cs] else cs.flatMap (outerMatches p) := by
  rw [outerMatches, outerMatchesList_eq]

variable {p}

theorem of_mem_outerMatches {s t : RoseTree α} (h : s ∈ outerMatches p t) : p s := by
  induction t with
  | node a cs ih =>
    rw [outerMatches_node] at h
    split_ifs at h with hp
    · exact (List.mem_singleton.1 h) ▸ hp
    · obtain ⟨c, hc, hs⟩ := List.mem_flatMap.1 h
      exact ih c hc hs

/-- The first subtree in preorder satisfying `p` is an outermost one. -/
theorem mem_outerMatches_of_find? {s t : RoseTree α}
    (h : t.subtrees.find? (fun u ↦ decide (p u)) = some s) : s ∈ outerMatches p t := by
  induction t with
  | node a cs ih =>
    rw [subtrees_node, List.find?_cons] at h
    rw [outerMatches_node]
    split_ifs with hp
    · simp only [hp, decide_true] at h
      exact List.mem_singleton.2 (Option.some.inj h).symm
    · simp only [hp, decide_false] at h
      clear hp
      induction cs with
      | nil => simp at h
      | cons c cs ihcs =>
        rw [List.flatMap_cons, List.find?_append] at h
        rw [List.flatMap_cons, List.mem_append]
        cases hc : (c.subtrees.find? fun u ↦ decide (p u)) with
        | some s' =>
          rw [hc, Option.some_or] at h
          exact .inl (ih c List.mem_cons_self (hc.trans h))
        | none =>
          rw [hc, Option.none_or] at h
          exact .inr (ihcs (fun c hc ↦ ih c (List.mem_cons_of_mem _ hc)) h)

variable (p) (r : RoseTree α)

private theorem leaves_replaceIf_list (cs : List (RoseTree α))
    (ih : ∀ c ∈ cs, (replaceIf p r c).leaves + ((outerMatches p c).map leaves).sum =
      c.leaves + (outerMatches p c).length • r.leaves) :
    (cs.map (leaves ∘ replaceIf p r)).sum + ((cs.flatMap (outerMatches p)).map leaves).sum =
      (cs.map leaves).sum + (cs.flatMap (outerMatches p)).length • r.leaves := by
  induction cs with
  | nil => simp
  | cons x xs ihxs =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
      List.length_append, add_nsmul, Function.comp_apply]
    rw [add_add_add_comm, ih x List.mem_cons_self,
      ihxs fun y hy ↦ ih y (List.mem_cons_of_mem _ hy), add_add_add_comm]

/-- Substitution trades the leaves of the replaced subtrees for copies of the replacement's. -/
theorem leaves_replaceIf (t : RoseTree α) :
    (replaceIf p r t).leaves + ((outerMatches p t).map leaves).sum =
      t.leaves + (outerMatches p t).length • r.leaves := by
  induction t with
  | node a cs ih =>
    rw [replaceIf_node, outerMatches_node]
    split_ifs
    · simp [add_comm, one_nsmul]
    · rcases cs with _ | ⟨c, cs⟩
      · simp
      · rw [List.map_cons, leaves_node_cons, leaves_node_cons, ← List.map_cons, List.map_map]
        exact leaves_replaceIf_list p r _ ih

/-- When the outermost matches all have the same leaves under `g`, the replacement has none, and
no `g`-value occurs twice among the leaves of `t`, replacing trades the leaves of one match. -/
theorem filterMap_leaves_replaceIf_add {β : Type*} [DecidableEq β] {g : α → Option β}
    {L : Multiset β} {s t : RoseTree α} (hL : ∀ u, p u → u.leaves.filterMap g = L)
    (hr : r.leaves.filterMap g = 0) (ht : (t.leaves.filterMap g).Nodup)
    (hs : s ∈ outerMatches p t) :
    (replaceIf p r t).leaves.filterMap g + s.leaves.filterMap g = t.leaves.filterMap g := by
  have key := congrArg (Multiset.filterMapAddMonoidHom g) (leaves_replaceIf p r t)
  have hom : ((outerMatches p t).map fun u ↦ u.leaves.filterMap g) =
      List.replicate (outerMatches p t).length L :=
    List.eq_replicate_iff.2 ⟨by simp, fun x hx ↦ by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
      exact hL u (of_mem_outerMatches hu)⟩
  simp only [map_add, map_nsmul, map_list_sum, List.map_map, Function.comp_def,
    Multiset.coe_filterMapAddMonoidHom, hr, nsmul_zero, add_zero] at key
  rw [hom, List.sum_replicate] at key
  rw [hL s (of_mem_outerMatches hs)]
  by_cases h0 : L = 0
  · rw [h0, nsmul_zero, add_zero] at key
    rw [h0, add_zero, key]
  · have hk : (outerMatches p t).length = 1 :=
      le_antisymm ((Multiset.nodup_of_le (key ▸ Multiset.le_add_left _ _) ht).le_one_of_nsmul h0)
        (List.length_pos_of_mem hs)
    rwa [hk, one_nsmul] at key

end OuterMatches

end RoseTree
