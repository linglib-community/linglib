/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Perm
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Leaf projections of a rose tree

`RoseTree.leavesWithDepth` collects the leaves of a rose tree as a multiset of pairs of a label
and its distance from the root. `RoseTree.leaves` forgets the distances, which leaves the
frontier `RoseTree.leafList` without its order. The number of leaves satisfying a predicate is
`Multiset.countP` on `leaves`.

## Main definitions

* `RoseTree.leavesWithDepth`, `RoseTree.leaves`: the projections.

## Main results

* `RoseTree.card_leavesWithDepth`: the projection has `numLeaves` elements.
* `RoseTree.coe_leafList`: the leaf labels are the frontier with its order forgotten.
* `RoseTree.numLeaves_le_numNodes`: a leaf is a vertex.
* `RoseTree.countP_leaves_lt_numNodes_of_not`: when the root fails the predicate, the
  counted leaves are among the non-root vertices.
* `RoseTree.leavesWithDepth_perm`, `RoseTree.leaves_perm`: both projections are
  `Perm`-invariant.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*} (a : α) (c : RoseTree α) (cs : List (RoseTree α))

/-! ### The projections -/

/-- The leaves of a rose tree, each paired with its distance from the root. -/
def leavesWithDepth : RoseTree α → Multiset (α × ℕ) :=
  fold fun a ps ↦
    match ps with
    | [] => {(a, 0)}
    | ps => (ps.map (Multiset.map fun p ↦ (p.1, p.2 + 1))).sum

/-- The multiset of leaf labels of a rose tree. -/
def leaves (t : RoseTree α) : Multiset α := t.leavesWithDepth.map Prod.fst

@[simp] theorem leavesWithDepth_leaf : leavesWithDepth (node a []) = {(a, 0)} := rfl

@[simp] theorem leavesWithDepth_node_cons :
    leavesWithDepth (node a (c :: cs))
      = ((c :: cs).map fun t ↦ t.leavesWithDepth.map fun p ↦ (p.1, p.2 + 1)).sum := by
  simp only [leavesWithDepth, fold_node, List.map_cons, List.map_map, Function.comp_def]

@[simp] theorem leaves_leaf : leaves (node a []) = {a} := rfl

@[simp] theorem leaves_node_cons :
    leaves (node a (c :: cs)) = ((c :: cs).map leaves).sum := by
  rw [leaves, leavesWithDepth_node_cons, ← Multiset.coe_mapAddMonoidHom, map_list_sum,
    List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ ↦ ?_)
  simp [leaves, Multiset.map_map]

/-! ### Cardinality -/

theorem card_leavesWithDepth (t : RoseTree α) :
    Multiset.card t.leavesWithDepth = t.numLeaves := by
  induction t with
  | node a cs ih =>
    rcases cs with _ | ⟨c, cs⟩
    · rfl
    · rw [leavesWithDepth_node_cons, numLeaves_node]
      have hsum : ∀ ds : List (RoseTree α), (∀ d ∈ ds, Multiset.card d.leavesWithDepth
            = d.numLeaves) →
          Multiset.card ((ds.map fun t ↦ t.leavesWithDepth.map fun p ↦ (p.1, p.2 + 1)).sum)
            = (ds.map numLeaves).sum := by
        intro ds hds
        induction ds with
        | nil => rfl
        | cons d ds ihd =>
          simp only [List.map_cons, List.sum_cons, Multiset.card_add, Multiset.card_map]
          rw [hds d List.mem_cons_self, ihd fun x hx ↦ hds x (List.mem_cons_of_mem _ hx)]
      rw [hsum (c :: cs) ih]
      have : 0 < ((c :: cs).map numLeaves).sum := by
        simp only [List.map_cons, List.sum_cons]
        have := numLeaves_pos c
        omega
      omega

theorem card_leaves (t : RoseTree α) : Multiset.card t.leaves = t.numLeaves := by
  rw [leaves, Multiset.card_map, card_leavesWithDepth]

theorem coe_leafList (t : RoseTree α) : (t.leafList : Multiset α) = t.leaves := by
  induction t with
  | node a cs ih =>
    rcases cs with _ | ⟨c, cs⟩
    · rfl
    · rw [leafList_node_cons, leaves_node_cons, ← List.map_congr_left ih]
      generalize c :: cs = ds
      induction ds with
      | nil => rfl
      | cons d ds ihd =>
        rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ihd]
        simp

theorem numLeaves_le_numNodes (t : RoseTree α) : t.numLeaves ≤ t.numNodes := by
  induction t with
  | node a cs ih =>
    rw [numLeaves_node, numNodes_node]
    have := List.sum_le_sum (f := numLeaves) (g := numNodes) ih
    omega

/-! ### `Perm` invariance -/

theorem leavesWithDepth_perm {t s : RoseTree α} (h : Perm t s) :
    t.leavesWithDepth = s.leavesWithDepth := by
  refine fold_perm (fun v l₁ l₂ h' ↦ ?_) h
  cases l₁ with
  | nil => rw [← h'.nil_eq]
  | cons x xs =>
    cases l₂ with
    | nil => exact absurd h'.eq_nil (by simp)
    | cons y ys => exact (h'.map (Multiset.map fun p : α × ℕ ↦ (p.1, p.2 + 1))).sum_eq

theorem leaves_perm {t s : RoseTree α} (h : Perm t s) : t.leaves = s.leaves :=
  congrArg (Multiset.map Prod.fst) (leavesWithDepth_perm h)

/-! ### Leaf statistics by predicate -/

section Statistics
variable (p : α → Prop) [DecidablePred p]

theorem countP_leaves_leaf (a : α) :
    (leaves (node a [])).countP p = if p a then 1 else 0 := by
  simp only [leaves_leaf, ← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero,
    Nat.zero_add]

@[simp] theorem countP_leaves_node_cons (a : α) (c : RoseTree α) (cs : List (RoseTree α)) :
    (leaves (node a (c :: cs))).countP p = ((c :: cs).map fun t ↦ t.leaves.countP p).sum := by
  rw [leaves_node_cons, ← Multiset.coe_countPAddMonoidHom, map_list_sum, List.map_map]
  rfl

theorem countP_leaves_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    (leaves (node a cs)).countP p = (cs.map fun t ↦ t.leaves.countP p).sum := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [countP_leaves_node_cons]

theorem countP_leaves_node_of_not {a : α} (cs : List (RoseTree α)) (h : ¬p a) :
    (leaves (node a cs)).countP p = (cs.map fun t ↦ t.leaves.countP p).sum := by
  cases cs with
  | nil => rw [countP_leaves_leaf, ite_eq_right h]; rfl
  | cons c cs => rw [countP_leaves_node_cons]

theorem countP_leaves_eq_numLeaves {t : RoseTree α} :
    t.leaves.countP p = t.numLeaves ↔ ∀ a ∈ t.leaves, p a := by
  rw [← card_leaves t]
  exact Multiset.countP_eq_card

@[simp] theorem card_filter_leavesWithDepth (t : RoseTree α) :
    Multiset.card (t.leavesWithDepth.filter fun q : α × ℕ ↦ p q.1) = t.leaves.countP p := by
  rw [leaves, Multiset.countP_map]

theorem sum_map_countP_leaves_le_node (a : α) (cs : List (RoseTree α)) :
    (cs.map fun t ↦ t.leaves.countP p).sum ≤ (leaves (node a cs)).countP p := by
  rcases cs with _ | ⟨c, cs⟩
  · exact Nat.zero_le _
  · exact (countP_leaves_node_cons p a c cs).ge

theorem countP_leaves_le_numNodes (t : RoseTree α) : t.leaves.countP p ≤ t.numNodes :=
  (Multiset.countP_le_card _ _).trans ((card_leaves t).trans_le (numLeaves_le_numNodes t))

theorem countP_leaves_lt_numNodes_of_not {a : α} (cs : List (RoseTree α)) (h : ¬p a) :
    (leaves (node a cs)).countP p < numNodes (node a cs) := by
  rw [countP_leaves_node_of_not p cs h, numNodes_node]
  have := List.sum_le_sum (l := cs) (f := fun t ↦ t.leaves.countP p) (g := numNodes)
    fun c _ ↦ countP_leaves_le_numNodes p c
  omega

end Statistics

end RoseTree
