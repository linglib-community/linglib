/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs

/-!
# Alignment constraints

This file defines Generalized Alignment, the constraint family requiring each constituent of one
category to share an edge with a constituent of another, assessed categorically.
`Constraint.align R` scores a pair of constituent families with one violation for each member of
the first family that bears `R` to no member of the second. Over the spans of a tree's
constituents (`RoseTree.spans`), `R` comparing right edges gives Align-R, comparing left edges
Align-L, and equality gives the Match constraints of Match Theory, which require both edges to
coincide with those of one constituent of the other family. A constraint on candidates of another
type is the `Constraint.comap` of `align R` along the candidate's two families.

## Main definitions

* `Constraint.align`: Generalized Alignment of one family of constituents to another along `R`.
* `Constraint.alignLeft`, `Constraint.alignRight`: Align-L and Align-R over spans, the edges
  compared at their left or their right cut.

## Main results

* `Constraint.align_eq_zero_iff`: a pair satisfies `align R` iff each member of the first family
  bears `R` to a member of the second.

## References

* [mccarthy-prince-1993b]
* [selkirk-2011]
-/

@[expose] public section

namespace OptimalityTheory.Constraint

variable {β γ : Type*} (R : β → γ → Prop) [DecidableRel R]

/-- **Generalized Alignment** ([mccarthy-prince-1993b]) of one family of constituents to another
along `R`, assessed categorically: one violation for each member of the first family that bears
`R` to no member of the second. On spans, `R` comparing right or left edges is Align-R or
Align-L, and equality is the Match constraint ([selkirk-2011]). -/
def align : Constraint (List β × List γ) := fun x ↦ x.1.countP fun a ↦ ∀ b ∈ x.2, ¬ R a b

variable {R}

theorem align_eq_zero_iff {x : List β × List γ} : align R x = 0 ↔ ∀ a ∈ x.1, ∃ b ∈ x.2, R a b := by
  simp [align, List.countP_eq_zero]

/-- **Align-L** over spans, `Align(Cat₁, L, Cat₂, L)` ([mccarthy-prince-1993b]): one violation for
each span of the first family whose left cut begins no span of the second. -/
abbrev alignLeft : Constraint (List (ℕ × ℕ) × List (ℕ × ℕ)) := align fun a b ↦ a.1 = b.1

/-- **Align-R** over spans, `Align(Cat₁, R, Cat₂, R)` ([mccarthy-prince-1993b]): one violation for
each span of the first family whose right cut ends no span of the second. -/
abbrev alignRight : Constraint (List (ℕ × ℕ) × List (ℕ × ℕ)) := align fun a b ↦ a.2 = b.2

-- A phrase over two words is right-aligned with the second word, not left-aligned with it, and
-- matches neither.
example : alignRight ([(0, 2)], [(0, 1), (1, 2)]) = 0 := by decide
example : alignLeft ([(1, 2)], [(0, 2)]) = 1 := by decide
example : align Eq ([(0, 2)], [(0, 1), (1, 2)]) = 1 := by decide

end OptimalityTheory.Constraint
