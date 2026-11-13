/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Logic.Relation

/-!
# Rewriting a subtree of a rose tree

`RoseTree.Rewrites r t t'` holds when `t'` is `t` with one subtree `x` replaced by a `y` such that
`r x y`: the closure of `r` under the contexts of a rose tree. Chains of rewrites in the children
of a node [assemble into a chain at the node](##RoseTree.reflTransGen_rewrites_node).
-/

@[expose] public section

namespace RoseTree

variable {α : Type*} {r : RoseTree α → RoseTree α → Prop}

/-- `Rewrites r t t'` when `t'` is `t` with one subtree `x` replaced by a `y` such that `r x y`. -/
inductive Rewrites (r : RoseTree α → RoseTree α → Prop) : RoseTree α → RoseTree α → Prop
  /-- The replacement is at the root. -/
  | here {x y : RoseTree α} (h : r x y) : Rewrites r x y
  /-- The replacement is inside a child. -/
  | child (a : α) (l₁ : List (RoseTree α)) {c c' : RoseTree α} (l₂ : List (RoseTree α))
      (h : Rewrites r c c') : Rewrites r (node a (l₁ ++ c :: l₂)) (node a (l₁ ++ c' :: l₂))

theorem Rewrites.mono {r' : RoseTree α → RoseTree α → Prop} (hr : ∀ x y, r x y → r' x y)
    {t t' : RoseTree α} (h : Rewrites r t t') : Rewrites r' t t' := by
  induction h with
  | here h => exact .here (hr _ _ h)
  | child a l₁ l₂ _ ih => exact .child a l₁ l₂ ih

/-- A rewrite in the `i`-th child is a rewrite of the node. -/
theorem Rewrites.set (a : α) {cs : List (RoseTree α)} (i : Fin cs.length) {c' : RoseTree α}
    (h : Rewrites r cs[i] c') : Rewrites r (node a cs) (node a (cs.set i c')) := by
  have key := Rewrites.child a (cs.take i) (cs.drop (i + 1)) h
  rw [Fin.getElem_fin, List.getElem_cons_drop, List.take_append_drop] at key
  rw [List.set_eq_take_append_cons_drop]
  simpa only [Fin.is_lt, ↓reduceIte] using key

/-- Chains of rewrites in the children of a node give a chain of rewrites at the node. -/
theorem reflTransGen_rewrites_node (a : α) (pre : List (RoseTree α)) {cs cs' : List (RoseTree α)}
    (h : List.Forall₂ (Relation.ReflTransGen (Rewrites r)) cs cs') :
    Relation.ReflTransGen (Rewrites r) (node a (pre ++ cs)) (node a (pre ++ cs')) := by
  induction h generalizing pre with
  | nil => exact .refl
  | @cons c c' cs cs' h _ ih =>
    refine (h.lift (fun x ↦ node a (pre ++ x :: cs)) fun _ _ hx ↦ .child a pre cs hx).trans ?_
    simpa using ih (pre ++ [c'])

end RoseTree
