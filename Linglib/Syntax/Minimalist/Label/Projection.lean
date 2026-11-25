/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Head
public import Linglib.Syntax.Minimalist.SyntacticObject.Projection

/-!
# The head a projection relation gives

When two syntactic objects merge, at most one of them projects. A projection relation `P` says
which: `P x y` holds when `x` projects over `y`, and it is asymmetric. The accounts of labeling
differ in this relation, and the head of an object follows from it. A leaf heads itself, and a
Merge is headed by the head of the daughter that projects, so an object is headed by one of its
leaves or by none. The lexical item that heads an object is that leaf, where it is a lexical item
and not a trace.

## Main definitions

* `Minimalist.headLeaf`: the leaf that heads an object under a projection relation, on any leaves.
* `Minimalist.headItem`: the lexical item that heads it.

## Main results

* `Minimalist.bind_subAt?_headPath`: the leaf that heads an object is the leaf at the end of the
  head path of a planar form of it.
* `Minimalist.isHeadFunction_headItem`: the head item is a head function.

## Implementation notes

* Merge is commutative, so the head of a Merge cannot depend on an order of its daughters. The
  asymmetry of `P` is what makes the head well defined, and it leaves the Merge of an object with
  itself without a head.
* The relation is on objects. An account that reads the head daughter off the object a pair of
  sisters lies in, as labeling by minimal search does, gives head daughters at the positions of a
  planar object and no relation of this kind.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

section Leaves

variable {α : Type} (P : SyntacticObject α → SyntacticObject α → Prop) [DecidableRel P]
  [Std.Asymm P]

/-- The leaf that heads an object, where `P x y` says that `x` projects over `y`: a leaf heads
itself, and a Merge is headed by the head of the daughter that projects. -/
def headLeaf : SyntacticObject α → Option α :=
  FreeCommMagma.elim some (fun l r a b ↦ if P l r then a else if P r l then b else none)
    fun l r a b ↦ by
      by_cases h : P l r
      · simp [h, Std.Asymm.asymm _ _ h]
      · simp [h]

@[simp] theorem headLeaf_of (x : α) : headLeaf P (FreeCommMagma.of x) = some x := rfl

theorem headLeaf_mul (l r : SyntacticObject α) :
    headLeaf P (l * r) = if P l r then headLeaf P l else if P r l then headLeaf P r else none :=
  FreeCommMagma.elim_mul _ _ _ l r

/-- No object merged with itself has a head. -/
@[simp] theorem headLeaf_mul_self (x : SyntacticObject α) : headLeaf P (x * x) = none := by
  have hx : ¬ P x x := fun h ↦ Std.Asymm.asymm x x h h
  simp [headLeaf_mul, hx]

/-- The leaf that heads an object is the leaf at the end of the head path of any planar form of
it: the head read off the object and the head reached through the daughters that project are the
same leaf. -/
theorem bind_subAt?_headPath (t : PlanarSyntacticObject α) :
    (headPath P t).bind t.subAt? = (headLeaf P t.toSyntacticObject).map FreeMagma.of := by
  induction t using FreeMagma.recOnMul with
  | ih1 a => rfl
  | ih2 l r ihl ihr =>
    rw [headPath_mul, PlanarSyntacticObject.toSyntacticObject_mul, headLeaf_mul]
    split_ifs
    · rw [← ihl]
      cases headPath P l <;> rfl
    · rw [← ihr]
      cases headPath P r <;> rfl
    · rfl

end Leaves

variable {L ι : Type}
    (P : SyntacticObject (SyntacticObject.Leaf L ι) → SyntacticObject (SyntacticObject.Leaf L ι) →
    Prop) [DecidableRel P]
  [Std.Asymm P]

theorem headLeaf_merge (l r : SyntacticObject (SyntacticObject.Leaf L ι)) :
    headLeaf P (merge l r) = if P l r then headLeaf P l else if P r l then headLeaf P r else none :=
  headLeaf_mul P l r

/-- No object merged with itself has a head. -/
theorem headLeaf_merge_self (x : SyntacticObject (SyntacticObject.Leaf L ι)) : headLeaf P
    (merge x x) = none :=
  headLeaf_mul_self P x

/-- The lexical item that heads an object: its head leaf, where that is a lexical item. -/
def headItem (s : SyntacticObject (SyntacticObject.Leaf L ι)) : Option L :=
  (headLeaf P s).bind (Leaf.elim some fun _ ↦ none)

@[simp] theorem headItem_leaf (a : L) : headItem P
    (leaf a : SyntacticObject (SyntacticObject.Leaf L ι)) = some a := rfl

theorem headItem_merge (l r : SyntacticObject (SyntacticObject.Leaf L ι)) :
    headItem P (merge l r) =
      if P l r then headItem P l else if P r l then headItem P r else none := by
  rw [headItem, headLeaf_merge]
  split_ifs <;> rfl

/-- The head item of a projection relation is a head function. -/
theorem isHeadFunction_headItem : IsHeadFunction (headItem P) where
  eq_of_mem_leaf h := by simpa [eq_comm] using h
  mem_or_mem {x y a} h := by
    rw [headItem_merge] at h
    split_ifs at h
    · exact .inl h
    · exact .inr h
    · cases h

end Minimalist
