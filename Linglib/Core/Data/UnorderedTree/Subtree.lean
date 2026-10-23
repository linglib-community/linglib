/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.Data.Multiset.Bind

/-!
# Subtrees of nonplanar trees

`UnorderedTree.subtrees t` is the multiset of all subtrees of `t`, the root included, one per
vertex, so its cardinality is `t.numNodes`. It is computed on a planar representative by
`RoseTree.unorderedSubtrees`, which also serves proofs that recurse over planar children.

## Main definitions

* `UnorderedTree.subtrees`, `RoseTree.unorderedSubtrees`

## Main results

* `UnorderedTree.subtrees_node`: a node's subtrees are the node itself and its children's
  subtrees.
* `UnorderedTree.card_subtrees`: one subtree per vertex.
* `RoseTree.mem_unorderedSubtrees`: the nonplanar subtrees of a planar tree are the images of its
  subtrees at its positions.

## Implementation notes

`subtrees` is lifted from the planar recursion, not defined by `UnorderedTree.para`, whose
tupling rebuilds every subtree with `node` and so slows kernel `decide` on c-command. It is
well-defined because the planar recursion computes the paramorphism.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

mutual
/-- The nonplanar subtrees of a planar tree, root included. -/
def unorderedSubtrees : RoseTree α → Multiset (UnorderedTree α)
  | .node a cs => UnorderedTree.mk (.node a cs) ::ₘ unorderedSubtreesList cs
/-- The nonplanar subtrees of a list of trees. -/
def unorderedSubtreesList : List (RoseTree α) → Multiset (UnorderedTree α)
  | []      => 0
  | c :: cs => unorderedSubtrees c + unorderedSubtreesList cs
end

mutual
theorem unorderedSubtrees_eq_map (p : RoseTree α) :
    unorderedSubtrees p = (p.subtrees.map UnorderedTree.mk : Multiset (UnorderedTree α)) := by
  obtain ⟨a, cs⟩ := p
  rw [unorderedSubtrees, subtrees_node, List.map_cons, ← Multiset.cons_coe,
    unorderedSubtreesList_eq_map]
theorem unorderedSubtreesList_eq_map (cs : List (RoseTree α)) :
    unorderedSubtreesList cs =
      ((cs.flatMap subtrees).map UnorderedTree.mk : Multiset (UnorderedTree α)) := by
  match cs with
  | [] => rfl
  | c :: cs =>
    rw [unorderedSubtreesList, unorderedSubtrees_eq_map, unorderedSubtreesList_eq_map,
      List.flatMap_cons, List.map_append, Multiset.coe_add]
end

theorem mem_unorderedSubtrees {p : RoseTree α} {x : UnorderedTree α} :
    x ∈ unorderedSubtrees p ↔ ∃ q s, p.subtreeAt q = some s ∧ UnorderedTree.mk s = x := by
  simp only [unorderedSubtrees_eq_map, Multiset.mem_coe, List.mem_map, mem_subtrees,
    isSubtree_iff_exists_subtreeAt]
  exact ⟨fun ⟨s, ⟨q, hq⟩, hx⟩ ↦ ⟨q, s, hq, hx⟩, fun ⟨q, s, hq, hx⟩ ↦ ⟨s, ⟨q, hq⟩, hx⟩⟩

end RoseTree

open RoseTree

namespace UnorderedTree

variable {α : Type*}

private theorem unorderedSubtrees_eq_para (t : RoseTree α) : unorderedSubtrees t =
    para (fun a ps ↦ node a (ps.map Prod.fst) ::ₘ (ps.map Prod.snd).sum) (mk t) := by
  induction t with
  | node a cs ih =>
    rw [← node_mk_tree_list, para_node, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, Multiset.map_id', node_mk_tree_list, unorderedSubtrees]
    congr 1
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      rw [List.map_cons, ← Multiset.cons_coe, Multiset.map_cons, Multiset.sum_cons,
        unorderedSubtreesList, ih c List.mem_cons_self,
        ihcs fun c hc ↦ ih c (List.mem_cons_of_mem _ hc)]

/-- All subtrees of a nonplanar tree, root included. -/
def subtrees : UnorderedTree α → Multiset (UnorderedTree α) :=
  Quotient.lift unorderedSubtrees fun _ _ h ↦ by
    rw [unorderedSubtrees_eq_para, unorderedSubtrees_eq_para, mk, mk, Quotient.sound h]

@[simp] theorem subtrees_mk (t : RoseTree α) : subtrees (mk t) = unorderedSubtrees t := rfl

@[simp] theorem subtrees_node (a : α) (F : Multiset (UnorderedTree α)) :
    subtrees (node a F) = node a F ::ₘ (F.map subtrees).sum := by
  have h (t : UnorderedTree α) :
      subtrees t = para (fun a ps ↦ node a (ps.map Prod.fst) ::ₘ (ps.map Prod.snd).sum) t :=
    Quotient.inductionOn t unorderedSubtrees_eq_para
  simp only [h, para_node, Multiset.map_map, Function.comp_def, Multiset.map_id']

theorem subtrees_leaf (a : α) : subtrees (leaf a) = {leaf a} := by
  simpa using subtrees_node a 0

theorem subtrees_node_pair (a : α) (l r : UnorderedTree α) :
    subtrees (node a {l, r}) = node a {l, r} ::ₘ (subtrees l + subtrees r) := by
  simp [Multiset.insert_eq_cons]

@[simp] theorem mem_subtrees_leaf {m : UnorderedTree α} {a : α} :
    m ∈ subtrees (leaf a) ↔ m = leaf a := by
  rw [subtrees_leaf, Multiset.mem_singleton]

@[simp] theorem mem_subtrees_node_pair {m : UnorderedTree α} {a : α} {l r : UnorderedTree α} :
    m ∈ subtrees (node a {l, r}) ↔ m = node a {l, r} ∨ m ∈ subtrees l ∨ m ∈ subtrees r := by
  rw [subtrees_node_pair, Multiset.mem_cons, Multiset.mem_add]

theorem self_mem_subtrees (t : UnorderedTree α) : t ∈ subtrees t := by
  induction t with
  | node a F _ => simp

/-- One subtree per vertex. -/
theorem card_subtrees (t : UnorderedTree α) : (subtrees t).card = t.numNodes := by
  induction t with
  | node a F ih =>
    rw [subtrees_node, Multiset.card_cons, numNodes_node,
      show (F.map subtrees).sum.card = ((F.map subtrees).map Multiset.card).sum from
        Multiset.card_join _, Multiset.map_map]
    exact congrArg (·.sum + 1) (Multiset.map_congr rfl ih)

end UnorderedTree
