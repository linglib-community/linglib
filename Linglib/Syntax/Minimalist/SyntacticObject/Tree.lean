/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Multiset.ZeroCons
public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# The trees of syntactic objects

A planar syntactic object on the leaves `α` has an ordered tree and a syntactic object an unordered
one, over `Option α`: a leaf carries its item and a Merge carries nothing. An object is [determined
by its tree](##Minimalist.SyntacticObject.toUnorderedTree_injective), and the subtree at an address
is [the tree of the planar object there](##Minimalist.PlanarSyntacticObject.getElem?_toRoseTree),
so what is said of a subtree is said of an object. Dominance, precedence and command on the
positions of `p.toRoseTree` are those of the tree.

## Main definitions

* `Minimalist.PlanarSyntacticObject.toRoseTree`: the ordered tree of a planar object.
* `Minimalist.SyntacticObject.toUnorderedTree`: the unordered tree of an object.
* `Minimalist.PlanarSyntacticObject.daughters`: the two daughters of a Merge, in order.
* `Minimalist.PlanarSyntacticObject.subAt?`: the planar object at an address.

## Implementation notes

* There is no map back from trees: a function on the trees of objects is written on the objects,
  by recursion on the free magma.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

variable {α : Type}

namespace PlanarSyntacticObject

/-- The ordered tree of a planar object: a leaf carries its item, a Merge carries nothing. -/
def toRoseTree : PlanarSyntacticObject α → RoseTree (Option α)
  | .of a => .node (some a) []
  | .mul l r => .node none [toRoseTree l, toRoseTree r]

@[simp] theorem toRoseTree_of (a : α) :
    toRoseTree (FreeMagma.of a : PlanarSyntacticObject α) = .node (some a) [] := rfl

@[simp] theorem toRoseTree_mul (l r : PlanarSyntacticObject α) :
    (l * r).toRoseTree = .node none [l.toRoseTree, r.toRoseTree] := rfl

theorem toRoseTree_injective :
    Function.Injective (toRoseTree : PlanarSyntacticObject α → _) := by
  intro p
  induction p using FreeMagma.recOnMul with
  | ih1 x =>
    intro q h
    cases q with
    | of y => exact congrArg FreeMagma.of (by simpa [toRoseTree] using h)
    | mul l r => simp [toRoseTree] at h
  | ih2 l r hl hr =>
    intro q h
    cases q with
    | of y => simp [toRoseTree] at h
    | mul l' r' =>
      obtain ⟨h₁, h₂⟩ : toRoseTree l = toRoseTree l' ∧ toRoseTree r = toRoseTree r' := by
        simpa [toRoseTree] using h
      rw [hl h₁, hr h₂]; rfl

/-- The daughters of a planar object: none of a leaf, two of a Merge. -/
def daughters : PlanarSyntacticObject α → List (PlanarSyntacticObject α)
  | .of _ => []
  | .mul l r => [l, r]

@[simp] theorem daughters_of (a : α) :
    daughters (FreeMagma.of a : PlanarSyntacticObject α) = [] := rfl

@[simp] theorem daughters_mul (l r : PlanarSyntacticObject α) : (l * r).daughters = [l, r] := rfl

/-- The daughters of the tree are the trees of the daughters. -/
theorem children_toRoseTree (p : PlanarSyntacticObject α) :
    p.toRoseTree.children = p.daughters.map toRoseTree := by
  cases p <;> rfl

/-- A vertex of the tree of a planar object has no daughters or two. -/
theorem length_children_toRoseTree (p : PlanarSyntacticObject α) :
    p.toRoseTree.children.length = 0 ∨ p.toRoseTree.children.length = 2 := by
  cases p
  · exact .inl rfl
  · exact .inr rfl

/-- The planar object at an address of a planar object. -/
def subAt? : PlanarSyntacticObject α → List ℕ → Option (PlanarSyntacticObject α)
  | p, [] => some p
  | .mul l _, 0 :: q => subAt? l q
  | .mul _ r, 1 :: q => subAt? r q
  | _, _ => none

/-- The subtree at an address is the tree of the planar object there. -/
theorem getElem?_toRoseTree (p : PlanarSyntacticObject α) (q : List ℕ) :
    p.toRoseTree[q]? = (p.subAt? q).map toRoseTree := by
  induction p generalizing q with
  | of a => cases q <;> simp [toRoseTree, subAt?]
  | mul l r ihl ihr =>
    rcases q with _ | ⟨_ | _ | n, q⟩
    · rfl
    · exact (ihl q).trans rfl
    · exact (ihr q).trans rfl
    · show (RoseTree.node none [toRoseTree l, toRoseTree r])[(n + 2) :: q]? = none
      simp

end PlanarSyntacticObject

namespace SyntacticObject

/-- The unordered tree of a syntactic object. -/
def toUnorderedTree : SyntacticObject α → UnorderedTree (Option α) :=
  FreeCommMagma.elim (fun a ↦ UnorderedTree.leaf (some a))
    (fun _ _ l r ↦ UnorderedTree.node none {l, r})
    fun _ _ l r ↦ congrArg _ (Multiset.pair_comm l r)

@[simp] theorem toUnorderedTree_of (a : α) :
    toUnorderedTree (FreeCommMagma.of a) = UnorderedTree.leaf (some a) := rfl

@[simp] theorem toUnorderedTree_mul (l r : SyntacticObject α) :
    (l * r).toUnorderedTree = UnorderedTree.node none {l.toUnorderedTree, r.toUnorderedTree} :=
  FreeCommMagma.elim_mul ..

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toUnorderedTree_toSyntacticObject
    (p : PlanarSyntacticObject α) :
    p.toSyntacticObject.toUnorderedTree = UnorderedTree.mk p.toRoseTree := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => rfl
  | ih2 l r hl hr =>
    refine (toUnorderedTree_mul (PlanarSyntacticObject.toSyntacticObject l)
      (PlanarSyntacticObject.toSyntacticObject r)).trans ?_
    rw [hl, hr]
    exact UnorderedTree.node_pair_mk ..

/-- A syntactic object is determined by its tree. -/
theorem toUnorderedTree_injective :
    Function.Injective (toUnorderedTree : SyntacticObject α → _) :=
  FreeCommMagma.injective_of_mul_eq_mul
    (fun _ _ h ↦ Option.some.inj (by simpa using congrArg UnorderedTree.value h))
    (fun _ _ _ h ↦ by simpa using congrArg UnorderedTree.value h)
    fun _ _ _ _ h ↦ Multiset.pair_eq_pair_iff.1 (by simpa using congrArg UnorderedTree.children h)

@[simp] theorem toUnorderedTree_inj {s t : SyntacticObject α} :
    s.toUnorderedTree = t.toUnorderedTree ↔ s = t := toUnorderedTree_injective.eq_iff

end SyntacticObject

end Minimalist
