/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Linglib.Core.Data.Tree.Encodable

/-!
# Forests as binary trees

This file defines Knuth's natural correspondence between forests of rose trees and binary trees,
and deduces that rose trees over an encodable type are encodable. The binary tree of a nonempty
forest has the root of the first tree as its root, the binary tree of that tree's children as its
left subtree and the binary tree of the remaining trees as its right subtree: this is the
left-child right-sibling representation. A rose tree is its root value together with the forest of
its children, hence a value together with a binary tree.

## Main definitions

* `BinaryTree.ofForest`: the binary tree of a forest, with inverse `BinaryTree.toForest`, bundled
  as `BinaryTree.equivForest`.
* `RoseTree.equivProdBinaryTree`: a rose tree as a value together with a binary tree.
* `RoseTree.encodable`, `RoseTree.countable`: the instances transported along it.

## Main results

* `BinaryTree.numNodes_ofForest`: the correspondence preserves the number of nodes.

## References

* [knuth-1997]
-/

@[expose] public section

namespace BinaryTree

variable {α : Type*}

mutual

/-- The binary tree of a forest under the natural correspondence: `nil` for the empty forest,
otherwise its first tree `cons`ed onto the binary tree of the rest. -/
def ofForest : List (RoseTree α) → BinaryTree α
  | [] => nil
  | t :: rest => cons t (ofForest rest)

/-- `cons t r` is the binary tree of the forest `t :: toForest r`: a node with the root value of
`t`, the binary tree of the children of `t` on the left and `r` on the right. -/
def cons : RoseTree α → BinaryTree α → BinaryTree α
  | .node a cs, r => node a (ofForest cs) r

end

/-- The forest of a binary tree, inverse to `BinaryTree.ofForest`. -/
def toForest : BinaryTree α → List (RoseTree α)
  | nil => []
  | node a l r => RoseTree.node a (toForest l) :: toForest r

@[simp] theorem ofForest_nil : ofForest ([] : List (RoseTree α)) = nil := rfl

@[simp] theorem ofForest_cons (t : RoseTree α) (rest : List (RoseTree α)) :
    ofForest (t :: rest) = cons t (ofForest rest) := rfl

@[simp] theorem cons_node (a : α) (cs : List (RoseTree α)) (r : BinaryTree α) :
    cons (RoseTree.node a cs) r = node a (ofForest cs) r := rfl

@[simp] theorem toForest_nil : toForest (nil : BinaryTree α) = [] := rfl

@[simp] theorem toForest_node (a : α) (l r : BinaryTree α) :
    toForest (node a l r) = RoseTree.node a (toForest l) :: toForest r := rfl

mutual

@[simp] theorem toForest_ofForest : ∀ cs : List (RoseTree α), toForest (ofForest cs) = cs
  | [] => rfl
  | t :: rest => by rw [ofForest_cons, toForest_cons, toForest_ofForest rest]

@[simp] theorem toForest_cons : ∀ (t : RoseTree α) (r : BinaryTree α),
    toForest (cons t r) = t :: toForest r
  | .node a cs, r => by rw [cons_node, toForest_node, toForest_ofForest cs]

end

@[simp] theorem ofForest_toForest (t : BinaryTree α) : ofForest (toForest t) = t := by
  induction t <;> simp [*]

/-- The natural correspondence between binary trees and forests. -/
@[simps] def equivForest : BinaryTree α ≃ List (RoseTree α) :=
  ⟨toForest, ofForest, ofForest_toForest, toForest_ofForest⟩

mutual

theorem numNodes_ofForest :
    ∀ cs : List (RoseTree α), (ofForest cs).numNodes = (cs.map RoseTree.numNodes).sum
  | [] => rfl
  | t :: rest => by
    rw [ofForest_cons, numNodes_cons, numNodes_ofForest rest, List.map_cons, List.sum_cons]

theorem numNodes_cons : ∀ (t : RoseTree α) (r : BinaryTree α),
    (cons t r).numNodes = t.numNodes + r.numNodes
  | .node a cs, r => by
    rw [cons_node, numNodes, numNodes_ofForest cs, RoseTree.numNodes_node]; omega

end

end BinaryTree

namespace RoseTree

variable {α : Type*}

/-- A rose tree is its root value together with the binary tree of the forest of its children. -/
@[simps] def equivProdBinaryTree : RoseTree α ≃ α × BinaryTree α where
  toFun t := (t.value, .ofForest t.children)
  invFun p := node p.1 p.2.toForest
  left_inv t := by cases t; simp
  right_inv p := by simp

instance encodable [Encodable α] : Encodable (RoseTree α) := .ofEquiv _ equivProdBinaryTree

instance countable [Countable α] : Countable (RoseTree α) := by
  have := Encodable.ofCountable α
  infer_instance

end RoseTree
