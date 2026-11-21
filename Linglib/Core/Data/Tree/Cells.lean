/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The cells of a binary tree of tests

A binary tree whose nodes carry elements of a generalized Boolean algebra splits an element `c`
into cells, one per leaf: a node labelled `a` sends `c ⊓ a` to its left subtree and `c \ a` to
its right subtree. For sets this is the partition of `c` by a decision tree whose nodes test
membership in a set.

## Main definitions

* `BinaryTree.cells`: the cells of an element under a tree, from left to right.

## Main results

* `BinaryTree.pairwise_disjoint_cells`: the cells are pairwise disjoint.
* `BinaryTree.foldr_sup_cells`: the cells join to the element they split.
-/

@[expose] public section

namespace BinaryTree

variable {α : Type*} [GeneralizedBooleanAlgebra α]

/-- The cells into which a tree splits `c`, one per leaf from left to right: a node labelled `a`
sends `c ⊓ a` to its left subtree and `c \ a` to its right subtree. -/
def cells : BinaryTree α → α → List α
  | nil, c => [c]
  | node a l r, c => cells l (c ⊓ a) ++ cells r (c \ a)

@[simp] theorem cells_nil (c : α) : cells nil c = [c] := rfl

@[simp] theorem cells_node (a : α) (l r : BinaryTree α) (c : α) :
    cells (node a l r) c = cells l (c ⊓ a) ++ cells r (c \ a) := rfl

@[simp] theorem length_cells (t : BinaryTree α) (c : α) : (cells t c).length = t.numLeaves := by
  induction t generalizing c with
  | nil => rfl
  | node a l r ihl ihr => simp [numLeaves, ihl, ihr]

theorem le_of_mem_cells {t : BinaryTree α} {c x : α} (h : x ∈ cells t c) : x ≤ c := by
  induction t generalizing c with
  | nil => exact (List.mem_singleton.1 h).le
  | node a l r ihl ihr =>
    rcases List.mem_append.1 h with h | h
    exacts [(ihl h).trans inf_le_left, (ihr h).trans sdiff_le]

/-- The cells of a tree are pairwise disjoint. -/
theorem pairwise_disjoint_cells (t : BinaryTree α) (c : α) : (cells t c).Pairwise Disjoint := by
  induction t generalizing c with
  | nil => simp
  | node a l r ihl ihr =>
    refine List.pairwise_append.2 ⟨ihl _, ihr _, fun x hx y hy ↦ ?_⟩
    exact (disjoint_sdiff_self_right.mono_left inf_le_right).mono (le_of_mem_cells hx)
      (le_of_mem_cells hy)

private theorem foldr_sup (l : List α) (b : α) :
    l.foldr (· ⊔ ·) b = l.foldr (· ⊔ ·) ⊥ ⊔ b := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, sup_assoc]

/-- The cells of a tree join to the element they split. -/
theorem foldr_sup_cells (t : BinaryTree α) (c : α) : (cells t c).foldr (· ⊔ ·) ⊥ = c := by
  induction t generalizing c with
  | nil => simp
  | node a l r ihl ihr =>
    rw [cells_node, List.foldr_append, foldr_sup, ihl, ihr, sup_inf_sdiff]

end BinaryTree
