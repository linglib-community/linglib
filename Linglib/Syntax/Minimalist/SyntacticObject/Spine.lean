/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Spine
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# The spine of a syntactic object

Given the head daughter of each node, the heads of a tree are read off from the bottom up: a head
sits on the heads of its sister, and a phrase keeps those of its head daughter. This is a spine of
lexical items, for any type of them. The spine of a syntactic object in categories lists the heads
of its extended projection: a head projects its category over the spine of its sister, Keine's
Category Inheritance. It is the extended projection at the top of the spine of items, read in
categories.

## Main definitions

* `Minimalist.toSpine`: the spine of lexical items of a tree.
* `Minimalist.spineOf`: the spine of a tree in categories, by category inheritance.
* `Minimalist.spineAt`: the spine of the node at a position.

## Main results

* `Minimalist.spineOf_eq`: the spine in categories is the extended projection of the spine of
  items.
* `Minimalist.isExtendedProjection_spineOf`: the spine of a tree is an extended projection.
* `Minimalist.spineOf_le_spineOf_node`: the phrase of a head that inherits from its complement
  carries every category the complement does.

## References

* [keine-2019]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject

section

variable {L ι : Type} (η : RoseTree (Vertex L ι) → Option ℕ)

/-- The lexical item at the root of a tree, if it is a pronounced leaf. -/
def rootLex? : RoseTree (Vertex L ι) → Option L
  | .node (.inl a) _ => a
  | _ => none

/-- The spine of lexical items of a tree, its heads from the bottom up, given the index `η` of the
head daughter of each tree: a head sits on the heads of its sister, and a phrase keeps those of
its head daughter. -/
def toSpine : RoseTree (Vertex L ι) → Spine L
  | .node (.inl (some a)) _ => ⟨[a]⟩
  | .node (.inl none) [l, r] =>
    match η (.node (.inl none) [l, r]) with
    | some 0 => (rootLex? l).elim (toSpine l) fun a ↦ (toSpine r).append [a]
    | some 1 => (rootLex? r).elim (toSpine r) fun a ↦ (toSpine l).append [a]
    | _ => ⟨[]⟩
  | _ => ⟨[]⟩

end

variable (η : RoseTree (Vertex LexicalItem.Token) → Option ℕ) (t : PlanarSyntacticObject TokenLeaf)

/-- The spine of a tree, the heads of its extended projection, given the index `η` of the head
daughter of each tree: a head projects its category over the spine of its sister, and a phrase
keeps the spine of its head daughter ([keine-2019]'s Category Inheritance). -/
def spineOf : RoseTree (Vertex LexicalItem.Token) → Spine Cat
  | .node (.inl (some tok)) _ => ⟨[tok.item.cat]⟩
  | .node (.inl none) [l, r] =>
    match η (.node (.inl none) [l, r]) with
    | some 0 => (rootLex? l).elim (spineOf l) fun tok ↦ (spineOf r).project tok.item.cat
    | some 1 => (rootLex? r).elim (spineOf r) fun tok ↦ (spineOf l).project tok.item.cat
    | _ => ⟨[]⟩
  | _ => ⟨[]⟩

/-- The spine of the node at `p`. -/
def spineAt (p : GornAddress) : Spine Cat := t.toRoseTree[p]?.elim ⟨[]⟩ (spineOf η)

variable {η t} {l r : RoseTree (Vertex LexicalItem.Token)} {tok : LexicalItem.Token}

variable (η) in
/-- The spine of a tree in categories is the extended projection at the top of its spine of
lexical items, read in categories. -/
theorem spineOf_eq (s : RoseTree (Vertex LexicalItem.Token)) :
    spineOf η s = ((toSpine η s).map (·.item.cat)).extendedProjection := by
  fun_induction toSpine η s with
  | case1 a cs => simp [spineOf, Spine.map, Spine.extendedProjection, Spine.project, Spine.Inherits]
  | case2 l r h ihl ihr =>
    rw [spineOf, h]
    rcases l with ⟨(_ | tok) | _, _⟩ <;> simp_all [rootLex?, Spine.map, Spine.append]
  | case3 l r h ihl ihr =>
    rw [spineOf, h]
    rcases r with ⟨(_ | tok) | _, _⟩ <;> simp_all [rootLex?, Spine.map, Spine.append]
  | case4 l r h0 h1 =>
    rw [spineOf]
    split <;> simp_all [Spine.map]
  | case5 s h0 h1 =>
    rw [spineOf]
    · simp [Spine.map]
    · exact fun tok cs hs ↦ h0 tok cs hs
    · exact fun l r hs ↦ h1 l r hs

/-- The spine of a tree is an extended projection. -/
theorem isExtendedProjection_spineOf (s : RoseTree (Vertex LexicalItem.Token)) :
    (spineOf η s).IsExtendedProjection :=
  spineOf_eq η s ▸ Spine.isExtendedProjection_extendedProjection _

theorem spineOf_node_zero (h : η (.node (.inl none) [l, r]) = some 0) :
    spineOf η (.node (.inl none) [l, r]) =
      (rootLex? l).elim (spineOf η l) fun tok ↦ (spineOf η r).project tok.item.cat := by
  simp [spineOf, h]

theorem spineOf_node_one (h : η (.node (.inl none) [l, r]) = some 1) :
    spineOf η (.node (.inl none) [l, r]) =
      (rootLex? r).elim (spineOf η r) fun tok ↦ (spineOf η l).project tok.item.cat := by
  simp [spineOf, h]

/-- Horizon inheritance: the phrase of a head that inherits from its complement carries every
category the complement does, so it is a horizon for every probe the complement is. -/
theorem spineOf_le_spineOf_node (h : η (.node (.inl none) [l, r]) = some 0)
    (hl : rootLex? l = some tok) (hi : (spineOf η r).Inherits tok.item.cat) :
    spineOf η r ≤ spineOf η (.node (.inl none) [l, r]) := by
  simpa [spineOf_node_zero h, hl] using Spine.le_project hi

end Minimalist
