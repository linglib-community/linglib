/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.List.Matching

/-!
# Alignment constraints

This file defines Generalized Alignment, the constraint family requiring each constituent of one
category to share an edge with a constituent of another, assessed categorically.
`Constraint.align R` scores a pair of constituent families with one violation for each member of
the first family that bears `R` to no member of the second. Over the spans of a tree's
constituents (`RoseTree.spans`), `R` comparing right edges gives Align-R, comparing left edges
Align-L, and equality gives the Match constraints of Match Theory, which require both edges to
coincide with those of one constituent of the other family. `Constraint.deficiency R` counts
instead the members left without a partner when partners must be distinct, the MAX of a one-to-one
correspondence. A constraint on candidates of another type is the `Constraint.comap` of either
along the candidate's two families.

## Main definitions

* `Constraint.align`: Generalized Alignment of one family of constituents to another along `R`.
* `Constraint.alignLeft`, `Constraint.alignRight`: Align-L and Align-R over spans, the edges
  compared at their left or their right cut.
* `Constraint.deficiency`: the members of the first family left unpaired by a largest pairing
  with distinct members of the second along `R`.

## Main results

* `Constraint.align_eq_zero_iff`: a pair satisfies `align R` iff each member of the first family
  bears `R` to a member of the second.
* `Constraint.deficiency_le_align`: correspondence along `R` demands no more than alignment along
  a relation contained in `R` that pairs no two members with one, as identity does Match.

## References

* [mccarthy-prince-1993b]
* [mccarthy-prince-1995]
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

/-! ### One-to-one correspondence -/

section Deficiency

variable (R) [DecidableEq γ]

/-- **Correspondence** along `R` with each member of the second family answering to at most one of
the first, the MAX of [mccarthy-prince-1995] under UNIFORMITY: one violation for each member of the
first family left unpaired by a largest such pairing (`List.le_matchingNumber_iff`), the deficiency
of `R`. -/
def deficiency : Constraint (List β × List γ) := fun x ↦ x.1.length - x.1.matchingNumber R x.2

variable {R}

/-- **Correspondence asks no more than alignment along a stricter relation**: where `S` is
contained in `R` and no two members of a duplicate-free family bear `S` to one member, the members
left without a correspondent along `R` are among those bearing `S` to none. -/
theorem deficiency_le_align {S : β → γ → Prop} [DecidableRel S] {x : List β × List γ}
    (hx : x.1.Nodup) (hSR : ∀ a ∈ x.1, ∀ b, S a b → R a b)
    (hS : ∀ a ∈ x.1, ∀ a' ∈ x.1, ∀ b, S a b → S a' b → a = a') : deficiency R x ≤ align S x := by
  have h₁ := List.countP_le_matchingNumber hx hSR hS x.2
  have h₂ := List.length_eq_countP_add_countP (fun a ↦ decide (∃ b ∈ x.2, S a b)) (l := x.1)
  have h₃ : align S x = x.1.countP fun a ↦ ¬ decide (∃ b ∈ x.2, S a b) :=
    List.countP_congr fun a _ ↦ by simp
  simp only [deficiency, h₃]
  omega

end Deficiency

-- Two words inside one phrase both align to it, but only one can have it as correspondent.
example : align (fun a p : ℕ × ℕ ↦ p.1 ≤ a.1 ∧ a.2 ≤ p.2) ([(0, 1), (1, 2)], [(0, 2)]) = 0 := by
  decide
example : deficiency (fun a p : ℕ × ℕ ↦ p.1 ≤ a.1 ∧ a.2 ≤ p.2) ([(0, 1), (1, 2)], [(0, 2)])
    = 1 := by
  decide

end OptimalityTheory.Constraint
