/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Core.Data.RoseTree.Leaves
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Substitution of subtrees

`UnorderedTree.replace target replacement t` rebuilds `t` with every subtree equal to `target`
replaced by `replacement`. It is computed on a planar representative by
`RoseTree.unorderedReplace`, and is well-defined because that recursion computes the
`UnorderedTree.para` testing each subtree before rebuilding it from its substituted children.
The planar substitution `RoseTree.replaceIf` replaces the subtrees satisfying a predicate, and
replacing the planar subtrees in a class is `replace` on the class (`UnorderedTree.mk_replaceIf`).

## Main definitions

* `UnorderedTree.replace`, `RoseTree.unorderedReplace`
* `RoseTree.replaceIf`, `RoseTree.outerMatches`: the planar substitution and the subtrees it
  replaces.

## Main results

* `UnorderedTree.mk_replaceIf`: the quotient map commutes with substitution.
* `RoseTree.leaves_replaceIf`: substitution trades the leaves of the replaced subtrees for those of
  the replacement.
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

end OuterMatches

variable [DecidableEq α]

mutual
/-- Substitution on a planar tree: replace every subtree equal, in the quotient, to `target` by
    `replacement`. -/
def unorderedReplace (target replacement : UnorderedTree α) :
    RoseTree α → UnorderedTree α
  | .node a cs =>
      if UnorderedTree.mk (RoseTree.node a cs) = target then replacement
      else UnorderedTree.node a (unorderedReplaceList target replacement cs)
/-- Substitution in each child, collected as a multiset. -/
def unorderedReplaceList (target replacement : UnorderedTree α) :
    List (RoseTree α) → Multiset (UnorderedTree α)
  | []      => 0
  | c :: cs => unorderedReplace target replacement c ::ₘ unorderedReplaceList target replacement cs
end

end RoseTree

open RoseTree

namespace UnorderedTree

variable {α : Type*} [DecidableEq α]

private theorem unorderedReplace_eq_para (target replacement : UnorderedTree α)
    (p : RoseTree α) : unorderedReplace target replacement p =
      para (fun a ps ↦ if node a (ps.map Prod.fst) = target then replacement
        else node a (ps.map Prod.snd)) (mk p) := by
  induction p with
  | node a cs ih =>
    rw [← node_mk_tree_list, para_node, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, Multiset.map_id', node_mk_tree_list, unorderedReplace]
    congr 2
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      rw [List.map_cons, ← Multiset.cons_coe, Multiset.map_cons, unorderedReplaceList,
        ih c List.mem_cons_self, ihcs fun c hc ↦ ih c (List.mem_cons_of_mem _ hc)]

/-- Replace every subtree equal to `target` by `replacement`. -/
def replace (target replacement : UnorderedTree α) : UnorderedTree α → UnorderedTree α :=
  Quotient.lift (unorderedReplace target replacement) fun _ _ h ↦ by
    rw [unorderedReplace_eq_para, unorderedReplace_eq_para, mk, mk, Quotient.sound h]

@[simp] theorem replace_mk (target replacement : UnorderedTree α) (p : RoseTree α) :
    replace target replacement (mk p) = unorderedReplace target replacement p := rfl

theorem replace_node (target replacement : UnorderedTree α) (a : α)
    (F : Multiset (UnorderedTree α)) :
    replace target replacement (node a F) =
      if node a F = target then replacement else node a (F.map (replace target replacement)) := by
  have h (t : UnorderedTree α) : replace target replacement t = para (fun a ps ↦
      if node a (ps.map Prod.fst) = target then replacement else node a (ps.map Prod.snd)) t :=
    Quotient.inductionOn t (unorderedReplace_eq_para target replacement)
  simp only [h, para_node, Multiset.map_map, Function.comp_def, Multiset.map_id']

theorem replace_leaf (target replacement : UnorderedTree α) (x : α) :
    replace target replacement (leaf x) = if leaf x = target then replacement else leaf x := by
  simpa using replace_node target replacement x 0

theorem replace_node_pair (target replacement : UnorderedTree α) (a : α) (l r : UnorderedTree α) :
    replace target replacement (node a {l, r})
      = if node a {l, r} = target then replacement
        else node a {replace target replacement l, replace target replacement r} := by
  simp [replace_node]

/-- Replacing the whole tree yields the replacement. -/
theorem replace_self (t r : UnorderedTree α) : replace t r t = r := by
  simpa [node_eta] using replace_node t r t.value t.children

/-- Replacing the planar subtrees in the class `target` is replacing `target` in the class. -/
theorem mk_replaceIf (target : UnorderedTree α) (r t : RoseTree α) :
    mk (replaceIf (mk · = target) r t) = replace target (mk r) (mk t) := by
  induction t with
  | node a cs ih =>
    rw [replaceIf_node, ← node_mk_tree_list a cs, replace_node, node_mk_tree_list]
    split_ifs
    · rfl
    · rw [← node_mk_tree_list, Multiset.map_coe, List.map_map, List.map_map]
      exact congrArg (node a ∘ Multiset.ofList) (List.map_congr_left fun c hc ↦ ih c hc)

end UnorderedTree
