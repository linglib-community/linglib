/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Data.W.Basic

/-!
# Binary trees are encodable

This file provides the `Encodable` and `Countable` instances for binary trees, which
`Mathlib.Data.Tree.Basic` lacks. A binary tree is a W-type whose shapes are a leaf, with no
children, and a node labelled by a value, with two children. W-types over encodable shapes with
finite encodable arities are encodable, so binary trees over an encodable type are encodable.

## Main definitions

* `BinaryTree.toWType`, `BinaryTree.ofWType`: a binary tree as a W-type and back.
* The `Encodable` and `Countable` instances for `BinaryTree α`.

`[UPSTREAM]` candidate for `Mathlib.Data.Tree.Basic`.
-/

@[expose] public section

namespace BinaryTree

variable {α : Type*}

/-- The arity of a binary-tree shape: a leaf has no children and a node two. -/
def WArity : Option α → Type
  | none => Empty
  | some _ => Bool

instance : ∀ a : Option α, Fintype (WArity a)
  | none => inferInstanceAs (Fintype Empty)
  | some _ => inferInstanceAs (Fintype Bool)

instance : ∀ a : Option α, Encodable (WArity a)
  | none => inferInstanceAs (Encodable Empty)
  | some _ => inferInstanceAs (Encodable Bool)

/-- A binary tree as a W-type: a leaf has the shape `none`, a node the shape of its value, with
its left subtree at `true` and its right subtree at `false`. -/
def toWType : BinaryTree α → WType (WArity (α := α))
  | nil => ⟨none, Empty.elim⟩
  | node a l r => ⟨some a, fun b ↦ cond b (toWType l) (toWType r)⟩

/-- A W-type of binary-tree shapes as a binary tree. -/
def ofWType : WType (WArity (α := α)) → BinaryTree α
  | ⟨none, _⟩ => nil
  | ⟨some a, f⟩ => node a (ofWType (f true)) (ofWType (f false))

theorem ofWType_toWType : ∀ t : BinaryTree α, ofWType (toWType t) = t
  | nil => rfl
  | node a l r => by simp [toWType, ofWType, ofWType_toWType l, ofWType_toWType r]

instance [Encodable α] : Encodable (BinaryTree α) :=
  Encodable.ofLeftInverse toWType ofWType ofWType_toWType

instance [Countable α] : Countable (BinaryTree α) := by
  have := Encodable.ofCountable α
  infer_instance

end BinaryTree
