/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Computability.Edge
public import Mathlib.Order.Interval.Basic

/-!
# Alignment constraints

A Generalized Alignment constraint `Align(Cat₁, Edge₁, Cat₂, Edge₂)` of [mccarthy-prince-1993b]
requires that for each constituent of the category `Cat₁` there be a constituent of `Cat₂` such
that `Edge₁` of the first and `Edge₂` of the second coincide. We take the two categories of a
candidate as two families of constituents and the coincidence of edges as a relation `R` between
them, and define `Constraint.align R` to count the members of the first family bearing `R` to no
member of the second, so that `align R (l, m) = 0` exactly when every member of `l` bears `R` to
some member of `m` (`Constraint.align_eq_zero_iff`). For two families of spans,
`Constraint.alignEdge e₁ e₂` takes for `R` the equality of the endpoint of the first span at the
edge `e₁` with the endpoint of the second at `e₂`. With `R` the equality of spans, both edges of
a constituent coinciding with those of one constituent of the other family, `align Eq` is the
Match constraint of [selkirk-2011].

## Implementation notes

`align` assesses a constituent categorically, one violation when it is aligned with nothing, the
assessment [mccarthy-2003] argues for. [mccarthy-prince-1993b] assess the alignment of feet and
of infixes by the distance between the two edges; for feet that count is
`Prosody.Footing.footOffsets`.

A candidate enters as a pair of lists, not of finsets, so that two constituents of the same span
are counted twice. A constraint on candidates of another type is the `Constraint.comap` of one of
these along the map giving the two families of a candidate.

## References

* [mccarthy-prince-1993b]
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

namespace OptimalityTheory.Constraint

variable {β γ β' γ' : Type*} (R : β → γ → Prop) [DecidableRel R]

/-- Alignment of one family of constituents to another along `R`, assessed categorically: one
violation for each member of the first family that bears `R` to no member of the second. -/
def align : Constraint (List β × List γ) := fun x ↦ x.1.countP fun a ↦ ∀ b ∈ x.2, ¬ R a b

variable {R}

theorem align_eq_zero_iff {x : List β × List γ} : align R x = 0 ↔ ∀ a ∈ x.1, ∃ b ∈ x.2, R a b := by
  simp [align, List.countP_eq_zero]

/-- The members of a family are those aligned with nothing and those aligned with something. -/
theorem align_add_countP (x : List β × List γ) :
    align R x + x.1.countP (fun a ↦ ∃ b ∈ x.2, R a b) = x.1.length := by
  have h₁ := List.length_eq_countP_add_countP (fun a ↦ decide (∃ b ∈ x.2, R a b)) (l := x.1)
  have h₂ : align R x = x.1.countP fun a ↦ ¬ decide (∃ b ∈ x.2, R a b) :=
    List.countP_congr fun a _ ↦ by simp
  omega

/-- Alignment of the images of two families is alignment along the pullback of the relation. -/
theorem align_map (f : β' → β) (g : γ' → γ) (l : List β') (m : List γ') :
    align R (l.map f, m.map g) = align (fun a b ↦ R (f a) (g b)) (l, m) := by
  simp [align, List.countP_map, Function.comp_def]

/-- (4): `Align(Cat₁, Edge₁, Cat₂, Edge₂)` of [mccarthy-prince-1993b] over spans, one violation
for each span of the first family whose endpoint at `e₁` is the endpoint at `e₂` of no span of
the second. -/
abbrev alignEdge {α : Type*} [LE α] [DecidableEq α] (e₁ e₂ : Edge) :
    Constraint (List (NonemptyInterval α) × List (NonemptyInterval α)) :=
  align fun a b ↦ e₁.endpoint a = e₂.endpoint b

-- A phrase over two words is right-aligned with the second word, not left-aligned with it, and
-- matches neither. A suffix begins where the foot before it ends.
example : alignEdge (α := ℕ) .right .right
    ([⟨(0, 2), by decide⟩], [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩]) = 0 := by
  decide
example : alignEdge (α := ℕ) .left .left ([⟨(1, 2), by decide⟩], [⟨(0, 2), by decide⟩]) = 1 := by
  decide
example : align Eq ([(⟨(0, 2), by decide⟩ : NonemptyInterval ℕ)],
    [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩]) = 1 := by
  decide
example : alignEdge (α := ℕ) .left .right ([⟨(2, 3), by decide⟩], [⟨(0, 2), by decide⟩]) = 0 := by
  decide

end OptimalityTheory.Constraint
