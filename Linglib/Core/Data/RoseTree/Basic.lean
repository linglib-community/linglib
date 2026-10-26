/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Nat

/-!
# Rose trees

A rose tree over `α` is a root carrying a value in `α` with an ordered list of child subtrees, the
n-ary counterpart of mathlib's `BinaryTree`. A leaf is `node a []`. The children are a `List`,
which keeps the type computable. The unordered rooted tree, whose children form a multiset, is the
quotient of this type by `RoseTree.Perm` (`UnorderedTree`).

The type is nested through `List`, so its recursor takes one motive for trees and one for lists.
`RoseTree.rec'` is the induction principle with the single hypothesis `∀ c ∈ cs, motive c`, and
`RoseTree.fold` is the catamorphism from which `map`, the counts and the frontier are defined.

## Main definitions

* `RoseTree`, `RoseTree.value`, `RoseTree.children`, `RoseTree.leaf`: the type, its projections
  and its leaves.
* `RoseTree.rec'`, `RoseTree.fold`: induction and the catamorphism.
* `RoseTree.map`: relabelling.
* `RoseTree.numNodes`, `RoseTree.numLeaves`, `RoseTree.height`, `RoseTree.arity`: the counts.
* `RoseTree.values`, `RoseTree.localTrees`, `RoseTree.leafList`: the node values in preorder, each
  node's value with the values of its children, and the frontier.
-/

@[expose] public section


/-- A rose tree has a root `value : α` and an ordered list of child subtrees. A leaf is
`node a []`. -/
inductive RoseTree (α : Type*) where
  | node (value : α) (children : List (RoseTree α))
  deriving Repr

compile_inductive% RoseTree

namespace RoseTree

variable {α : Type*} {β : Type*} {γ : Type*}

/-! ### Projections -/

/-- The value at the root. -/
def value : RoseTree α → α
  | .node a _ => a

/-- The ordered list of child subtrees at the root. -/
def children : RoseTree α → List (RoseTree α)
  | .node _ cs => cs

@[simp] theorem value_node (a : α) (cs : List (RoseTree α)) : (node a cs).value = a := rfl

@[simp] theorem children_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).children = cs := rfl

/-- A leaf is a root with no children. -/
abbrev leaf (a : α) : RoseTree α := .node a []

/-! ### Decidable equality

`deriving DecidableEq` does not fire through the nested `List` occurrence (as of Lean v4.35.0), so
the instance is built by mutual recursion on the tree and its child list. -/

section DecidableEq
variable [DecidableEq α]

mutual

/-- Decidable equality on trees (mutual with the child-list case). -/
protected def decEq : (t s : RoseTree α) → Decidable (t = s)
  | node a cs, node b ds =>
    if hab : a = b then
      match RoseTree.decEqList cs ds with
      | isTrue h => isTrue (by rw [hab, h])
      | isFalse h => isFalse fun he ↦ by injection he with _ hcd; exact h hcd
    else
      isFalse fun he ↦ by injection he with hab' _; exact hab hab'

/-- Decidable equality on child lists (mutual with the tree case). -/
protected def decEqList : (ts ss : List (RoseTree α)) → Decidable (ts = ss)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | c :: cs, d :: ds =>
    match RoseTree.decEq c d with
    | isFalse h => isFalse fun he ↦ by injection he with hcd _; exact h hcd
    | isTrue h =>
      match RoseTree.decEqList cs ds with
      | isTrue h2 => isTrue (by rw [h, h2])
      | isFalse h2 => isFalse fun he ↦ by injection he with _ htl; exact h2 htl

end

instance instDecidableEq : DecidableEq (RoseTree α) := RoseTree.decEq

end DecidableEq

/-! ### Size -/

theorem sizeOf_lt_of_mem [SizeOf α] {a : α} {cs : List (RoseTree α)} {c : RoseTree α}
    (hc : c ∈ cs) : sizeOf c < sizeOf (RoseTree.node a cs) := by
  have := List.sizeOf_lt_of_mem hc
  simp only [RoseTree.node.sizeOf_spec]
  omega

/-! ### The recursion principle -/

/-- Induction on a rose tree proves `motive t` for all `t` from `motive (node a cs)` given
`motive c` for every child `c ∈ cs`. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : RoseTree α → Sort*}
    (node : ∀ (a : α) (cs : List (RoseTree α)),
      (∀ c ∈ cs, motive c) → motive (RoseTree.node a cs)) :
    ∀ t, motive t
  | .node a cs => node a cs fun c _hc ↦ rec' node c
termination_by t => sizeOf t
decreasing_by exact sizeOf_lt_of_mem _hc

/-! ### Catamorphism

The structural operations (`map`, `numNodes`, `height`, …) are folds, and their equations at a
node come from `fold_node`. -/

mutual
/-- The catamorphism replaces each `node a cs` by `f a (folded children)`. -/
def fold (f : α → List β → β) : RoseTree α → β
  | .node a cs => f a (foldList f cs)
/-- `foldList` folds across a list of children. -/
def foldList (f : α → List β → β) : List (RoseTree α) → List β
  | [] => []
  | c :: cs => fold f c :: foldList f cs
end

theorem foldList_eq (f : α → List β → β) (cs : List (RoseTree α)) :
    foldList f cs = cs.map (fold f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [show foldList f (c :: cs) = fold f c :: foldList f cs from rfl,
      ih, List.map_cons]

@[simp] theorem fold_node (f : α → List β → β) (a : α) (cs : List (RoseTree α)) :
    fold f (node a cs) = f a (cs.map (fold f)) := by
  rw [show fold f (node a cs) = f a (foldList f cs) from rfl, foldList_eq]

theorem fold_hom (h : β → γ) {f : α → List β → β} {g : α → List γ → γ}
    (hfg : ∀ a ps, h (f a ps) = g a (ps.map h)) (t : RoseTree α) :
    h (fold f t) = fold g t := by
  induction t with
  | node a cs ih =>
    rw [fold_node, fold_node, hfg, List.map_map]
    exact congrArg (g a) (List.map_congr_left fun c hc ↦ ih c hc)

/-! ### Functoriality -/

/-- Relabel every node by `f`, preserving shape. -/
def map (f : α → β) : RoseTree α → RoseTree β :=
  fold fun a cs ↦ RoseTree.node (f a) cs

@[simp] theorem map_node (f : α → β) (a : α) (cs : List (RoseTree α)) :
    map f (node a cs) = node (f a) (cs.map (map f)) := by
  simp only [map, fold_node]

theorem id_map (t : RoseTree α) : map id t = t := by
  induction t with
  | node a cs ih =>
    rw [map_node, id_eq]
    congr 1
    exact (List.map_congr_left ih).trans (List.map_id cs)

theorem comp_map (f : α → β) (g : β → γ) (t : RoseTree α) :
    map (g ∘ f) t = map g (map f t) := by
  induction t with
  | node a cs ih =>
    rw [map_node, map_node, map_node, Function.comp_apply, List.map_map]
    congr 1
    exact List.map_congr_left ih

@[simp] theorem value_map (f : α → β) (t : RoseTree α) : (map f t).value = f t.value := by
  cases t; simp

theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (map f) := by
  cases isEmpty_or_nonempty α with
  | inl h => exact fun t _ _ ↦ (h.false t.value).elim
  | inr _ =>
    obtain ⟨g, hg⟩ := hf.hasLeftInverse
    exact Function.LeftInverse.injective (g := map g) fun t ↦ by
      rw [← comp_map, hg.comp_eq_id, id_map]

/-! ### Counting -/

/-- The number of nodes. A leaf counts as `1`. -/
def numNodes : RoseTree α → ℕ :=
  fold fun _ ns ↦ ns.sum + 1

@[simp] theorem numNodes_node (a : α) (cs : List (RoseTree α)) :
    numNodes (node a cs) = (cs.map numNodes).sum + 1 := by
  simp only [numNodes, fold_node]

theorem numNodes_pos (t : RoseTree α) : 0 < numNodes t := by
  cases t with
  | node a cs => rw [numNodes_node]; omega

/-- The node values in preorder list the root first, then each child's values left to right. -/
def values : RoseTree α → List α :=
  fold fun a ls ↦ a :: ls.flatten

@[simp] theorem values_node (a : α) (cs : List (RoseTree α)) :
    values (node a cs) = a :: (cs.map values).flatten := by
  simp only [values, fold_node]

theorem length_values (t : RoseTree α) : t.values.length = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [values_node, numNodes_node, List.length_cons, List.length_flatten,
      List.map_map, Function.comp_def]
    rw [show (cs.map fun c ↦ c.values.length) = cs.map numNodes from
      List.map_congr_left ih]

mutual
/-- The local trees of a tree pair each node's value with the values of its children, one entry
per node in preorder. -/
def localTrees : RoseTree α → List (α × List α)
  | .node a cs => (a, cs.map value) :: localTreesList cs
/-- `localTreesList` concatenates the local trees of a list of trees. -/
def localTreesList : List (RoseTree α) → List (α × List α)
  | [] => []
  | c :: cs => localTrees c ++ localTreesList cs
end

theorem localTreesList_eq (cs : List (RoseTree α)) :
    localTreesList cs = (cs.map localTrees).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [localTreesList, ih, List.map_cons, List.flatten_cons]

@[simp] theorem localTrees_node (a : α) (cs : List (RoseTree α)) :
    localTrees (node a cs) = (a, cs.map value) :: (cs.map localTrees).flatten := by
  rw [localTrees, localTreesList_eq]

theorem length_localTrees (t : RoseTree α) : t.localTrees.length = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [localTrees_node, numNodes_node, List.length_cons, List.length_flatten,
      List.map_map, Function.comp_def]
    rw [show (cs.map fun c ↦ c.localTrees.length) = cs.map numNodes from
      List.map_congr_left ih]

/-- The ordered frontier lists the leaf values from left to right. -/
def leafList : RoseTree α → List α :=
  fold fun a ls ↦ match ls with
    | [] => [a]
    | ls => ls.flatten

@[simp] theorem leafList_leaf (a : α) : leafList (node a []) = [a] := by
  simp only [leafList, fold_node, List.map_nil]

theorem leafList_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    leafList (node a cs) = (cs.map leafList).flatten := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [leafList, fold_node, List.map_cons]

@[simp] theorem leafList_node_cons (a : α) (c : RoseTree α) (cs : List (RoseTree α)) :
    leafList (node a (c :: cs)) = ((c :: cs).map leafList).flatten :=
  leafList_node_of_ne_nil a (List.cons_ne_nil c cs)

theorem leafList_ne_nil (t : RoseTree α) : t.leafList ≠ [] := by
  induction t with
  | node a cs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      rw [leafList_node_cons]
      exact List.flatten_ne_nil_iff.2 ⟨c.leafList, List.mem_map_of_mem (List.mem_cons_self ..),
        ih c (List.mem_cons_self ..)⟩

/-- The number of leaves. A single leaf counts as `1`. -/
def numLeaves : RoseTree α → ℕ :=
  fold fun _ ns ↦ max 1 ns.sum

@[simp] theorem numLeaves_node (a : α) (cs : List (RoseTree α)) :
    numLeaves (node a cs) = max 1 (cs.map numLeaves).sum := by
  simp only [numLeaves, fold_node]

@[simp] theorem numLeaves_leaf (a : α) : numLeaves (leaf a) = 1 := by simp

theorem numLeaves_pos (t : RoseTree α) : 0 < numLeaves t := by
  cases t with
  | node a cs =>
    rw [numLeaves_node]
    exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

theorem numLeaves_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    numLeaves (node a cs) = (cs.map numLeaves).sum := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [numLeaves_node, List.map_cons, List.sum_cons]
  have := numLeaves_pos c
  omega

theorem length_leafList (t : RoseTree α) : t.leafList.length = t.numLeaves := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    · rw [leafList_node_of_ne_nil a hcs, numLeaves_node_of_ne_nil a hcs, List.length_flatten,
        List.map_map]
      exact congrArg List.sum (List.map_congr_left ih)

/-! ### Height -/

/-- The height is the number of nodes on a longest path from the root to a leaf, so a leaf has
height `1`. This is the convention of `BinaryTree.height`, where `nil` has height `0`. -/
def height : RoseTree α → ℕ :=
  fold fun _ hs ↦ hs.foldr max 0 + 1

@[simp] theorem height_node (a : α) (cs : List (RoseTree α)) :
    height (node a cs) = (cs.map height).foldr max 0 + 1 := by
  simp only [height, fold_node]

theorem height_pos (t : RoseTree α) : 0 < t.height := by
  cases t with
  | node a cs => rw [height_node]; exact Nat.succ_pos _

theorem height_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.height < t.height := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [height_node]
    exact Nat.lt_succ_of_le (List.le_max_of_le (l := cs.map height) (List.mem_map_of_mem h) le_rfl)

/-! ### Arity -/

/-- The arity of the root is its number of children. A leaf has arity `0`. -/
def arity (t : RoseTree α) : ℕ := t.children.length

@[simp] theorem arity_node (a : α) (cs : List (RoseTree α)) : arity (node a cs) = cs.length := rfl

@[simp] theorem arity_map (f : α → β) (t : RoseTree α) : (map f t).arity = t.arity := by
  cases t with
  | node a cs => simp [arity, map_node]

/-! ### `map` preserves the counts -/

@[simp] theorem map_leaf (f : α → β) (a : α) : map f (leaf a) = leaf (f a) := rfl

@[simp] theorem numNodes_map (f : α → β) (t : RoseTree α) : (map f t).numNodes = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [map_node, numNodes_node, List.map_map]
    exact congrArg (· + 1) (congrArg List.sum (List.map_congr_left ih))

@[simp] theorem numLeaves_map (f : α → β) (t : RoseTree α) : (map f t).numLeaves = t.numLeaves := by
  induction t with
  | node a cs ih =>
    simp only [map_node, numLeaves_node, List.map_map]
    exact congrArg (max 1 ·) (congrArg List.sum (List.map_congr_left ih))

@[simp] theorem height_map (f : α → β) (t : RoseTree α) : (map f t).height = t.height := by
  induction t with
  | node a cs ih =>
    simp only [map_node, height_node, List.map_map]
    exact congrArg (· + 1) (congrArg (List.foldr max 0) (List.map_congr_left ih))

@[simp] theorem localTrees_map (f : α → β) (t : RoseTree α) :
    (map f t).localTrees = t.localTrees.map fun p ↦ (f p.1, p.2.map f) := by
  induction t with
  | node a cs ih =>
    simp only [map_node, localTrees_node, List.map_map, List.map_cons, List.map_flatten]
    refine congrArg₂ _ ?_ (congrArg List.flatten (List.map_congr_left fun c hc ↦ ih c hc))
    exact congrArg _ (List.map_congr_left fun c _ ↦ by cases c; rfl)

@[simp] theorem leafList_map (f : α → β) (t : RoseTree α) :
    (map f t).leafList = t.leafList.map f := by
  induction t with
  | node a cs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      simp only [map_node, List.map_cons, leafList_node_cons, List.map_flatten, List.map_map]
      exact congrArg List.flatten (congrArg₂ _ (ih c (List.mem_cons_self ..))
        (List.map_congr_left fun d hd ↦ ih d (List.mem_cons_of_mem _ hd)))

/-! ### Instances -/

instance [Inhabited α] : Inhabited (RoseTree α) := ⟨leaf default⟩

end RoseTree

