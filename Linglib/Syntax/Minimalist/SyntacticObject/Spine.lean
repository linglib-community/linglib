/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Spine
public import Linglib.Syntax.Minimalist.SyntacticObject.Position

/-!
# The spine of a syntactic object

The spine of a syntactic object lists the heads of its extended projection from the bottom up.
Given the head daughter of each node, a head projects its category over the spine of its sister
and a phrase keeps the spine of its head daughter, Keine's Category Inheritance. We define the
spine of a tree of vertices, and of the node at a position of a syntactic object, as a
`Spine Cat`.

## Main definitions

* `Minimalist.spineOf`: the spine of a tree, by category inheritance.
* `Minimalist.spineAt`: the spine of the node at a position.

## Main results

* `Minimalist.isExtendedProjection_spineOf`: the spine of a tree is an extended projection.
* `Minimalist.spineOf_le_spineOf_node`: the phrase of a head that inherits from its complement
  carries every category the complement does.

## References

* [keine-2019]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject

variable (η : RoseTree Vertex → Option ℕ) (t : PlanarSyntacticObject)

/-- The lexical item at the root of a tree, if it is a pronounced leaf. -/
def rootToken? : RoseTree Vertex → Option LexicalItem.Token
  | .node (.inl tok) _ => tok
  | _ => none

/-- The spine of a tree, the heads of its extended projection, given the index `η` of the head
daughter of each tree: a head projects its category over the spine of its sister, and a phrase
keeps the spine of its head daughter ([keine-2019]'s Category Inheritance). -/
def spineOf : RoseTree Vertex → Spine Cat
  | .node (.inl (some tok)) _ => ⟨[tok.item.cat]⟩
  | .node (.inl none) [l, r] =>
    match η (.node (.inl none) [l, r]) with
    | some 0 => (rootToken? l).elim (spineOf l) fun tok ↦ (spineOf r).project tok.item.cat
    | some 1 => (rootToken? r).elim (spineOf r) fun tok ↦ (spineOf l).project tok.item.cat
    | _ => ⟨[]⟩
  | _ => ⟨[]⟩

/-- The spine of the node at `p`. -/
def spineAt (p : GornAddress) : Spine Cat := t.toRoseTree[p]?.elim ⟨[]⟩ (spineOf η)

variable {η t} {l r : RoseTree Vertex} {tok : LexicalItem.Token}

/-- The spine of a tree is an extended projection. -/
theorem isExtendedProjection_spineOf (s : RoseTree Vertex) :
    (spineOf η s).IsExtendedProjection := by
  fun_induction spineOf η s
  case case1 => exact .singleton _
  case case2 ihl ihr | case3 ihl ihr =>
    cases rootToken? _ <;> first | assumption | exact .project ‹_› _
  all_goals exact .nil

theorem spineOf_node_zero (h : η (.node (.inl none) [l, r]) = some 0) :
    spineOf η (.node (.inl none) [l, r]) =
      (rootToken? l).elim (spineOf η l) fun tok ↦ (spineOf η r).project tok.item.cat := by
  simp [spineOf, h]

theorem spineOf_node_one (h : η (.node (.inl none) [l, r]) = some 1) :
    spineOf η (.node (.inl none) [l, r]) =
      (rootToken? r).elim (spineOf η r) fun tok ↦ (spineOf η l).project tok.item.cat := by
  simp [spineOf, h]

/-- Horizon inheritance: the phrase of a head that inherits from its complement carries every
category the complement does, so it is a horizon for every probe the complement is. -/
theorem spineOf_le_spineOf_node (h : η (.node (.inl none) [l, r]) = some 0)
    (hl : rootToken? l = some tok) (hi : (spineOf η r).Inherits tok.item.cat) :
    spineOf η r ≤ spineOf η (.node (.inl none) [l, r]) := by
  simpa [spineOf_node_zero h, hl] using Spine.le_project hi

end Minimalist
