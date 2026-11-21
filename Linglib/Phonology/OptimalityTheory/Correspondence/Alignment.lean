/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Core.Computability.Edge
public import Mathlib.Order.Interval.Basic

/-!
# Alignment constraints

A Generalized Alignment constraint `Align(Cat₁, Edge₁, Cat₂, Edge₂)` of [mccarthy-prince-1993b]
requires that for each constituent of the category `Cat₁` there be a constituent of `Cat₂` such
that `Edge₁` of the first and `Edge₂` of the second coincide. The coincidence of edges is a
relation between the constituents of the two categories, and the constraint is MAX of
[mccarthy-prince-1995] on that relation: one violation for each constituent of `Cat₁` related to
no constituent of `Cat₂`. `Align(Cat₂, Edge₂, Cat₁, Edge₁)` is DEP of the same relation.

For two families of spans we define `Correspondence.ofEdges e₁ e₂ l m`, the pairs of positions at
which the endpoint of the first span at the edge `e₁` is the endpoint of the second at `e₂`. The
relation of having the same span is the intersection of the relations of sharing the left and
the right edge (`Correspondence.ofRel_eq`), so that by `Correspondence.maxViol_anti` a constraint
requiring both edges to coincide, the Match constraint of [selkirk-2011], is violated at least as
often as alignment at either edge.

## Implementation notes

The constraints are assessed categorically, one violation for a constituent aligned with
nothing, the assessment [mccarthy-2003] argues for. [mccarthy-prince-1993b] assess the alignment
of feet and of infixes by the distance between the two edges; for feet that count is
`Prosody.Footing.footOffsets`.

The two families are lists and the relation is between their positions, so that two constituents
of the same span are counted twice. `Correspondence.maxViol_ofRel_get` and
`Correspondence.depViol_ofRel_get` evaluate the constraints as counts over the lists.

## References

* [mccarthy-prince-1993b]
* [mccarthy-prince-1995]
* [mccarthy-2003]
* [selkirk-2011]
-/

@[expose] public section

/-- The endpoint of a span at an edge, its start at the left and its end at the right. -/
def Edge.endpoint {α : Type*} [LE α] : Edge → NonemptyInterval α → α
  | .left, s => s.fst
  | .right, s => s.snd

@[simp] theorem Edge.endpoint_left {α : Type*} [LE α] (s : NonemptyInterval α) :
    Edge.left.endpoint s = s.fst := rfl

@[simp] theorem Edge.endpoint_right {α : Type*} [LE α] (s : NonemptyInterval α) :
    Edge.right.endpoint s = s.snd := rfl

namespace OptimalityTheory.Correspondence

variable {α : Type*} [LE α] [DecidableEq α]

/-- (4): the pairs of positions of two families of spans at which the endpoint of the first span
at `e₁` is the endpoint of the second at `e₂`. `Align(Cat₁, Edge₁, Cat₂, Edge₂)` of
[mccarthy-prince-1993b] is its MAX, and `Align(Cat₂, Edge₂, Cat₁, Edge₁)` its DEP. -/
abbrev ofEdges (e₁ e₂ : Edge) (l m : List (NonemptyInterval α)) :
    Correspondence (Fin l.length) (Fin m.length) :=
  ofRel (fun a b ↦ e₁.endpoint a = e₂.endpoint b) l.get m.get

/-- Two spans are equal exactly when they share both edges. -/
theorem ofRel_eq (l m : List (NonemptyInterval α)) :
    ofRel Eq l.get m.get = ofEdges .left .left l m ∩ ofEdges .right .right l m := by
  ext ⟨i, j⟩
  simp [NonemptyInterval.ext_iff, Prod.ext_iff]

-- A phrase over two words is right-aligned with the second word, not left-aligned with it, and
-- matches neither. A suffix begins where the foot before it ends.
example : (ofEdges (α := ℕ) .right .right [⟨(0, 2), by decide⟩]
    [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩]).maxViol = 0 := by
  decide
example : (ofEdges (α := ℕ) .left .left
    [⟨(1, 2), by decide⟩] [⟨(0, 2), by decide⟩]).maxViol = 1 := by
  decide
example : (ofRel Eq [(⟨(0, 2), by decide⟩ : NonemptyInterval ℕ)].get
    [(⟨(0, 1), by decide⟩ : NonemptyInterval ℕ), ⟨(1, 2), by decide⟩].get).maxViol = 1 := by
  decide
example : (ofEdges (α := ℕ) .left .right
    [⟨(2, 3), by decide⟩] [⟨(0, 2), by decide⟩]).maxViol = 0 := by
  decide

end OptimalityTheory.Correspondence
