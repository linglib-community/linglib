module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Linglib.Syntax.Category.Coordinator

/-!
# The denotation of a coordinator

A coordinator denotes an operation on the set of its coordinands, which its semantic type fixes:
the infimum of the set for a conjunctive or adversative coordinator, its supremum for a
disjunctive one, and the complement of its supremum for a negative one. Coordinating two
constituents is the case of a two-element set, so one operation conjoins truth values,
predicates and generalized quantifiers, coordinates lists of any length, and builds the
quantifiers that Japanese *ka* and *mo* form from indeterminate pronouns. The composition engine
applies it to two sisters of one conjoinable type in `Semantics/Composition/Coordination.lean`.
[Coordinating a constituent alone returns it](##denote_singleton), as
[coordinating it with itself does](##denote_pair_self), except under negative coordination, and
[the coordination of functions is computed pointwise](##denote_apply).

## Main definitions

* `Coordinator.denote`: what a coordinator denotes on a set of coordinands.

## Implementation notes

The denotation is the truth-conditional content only. The contrast an adversative coordinator
adds to conjunction is a relation between the coordinands in discourse, and
`denote_of_adversative` records that it is invisible here. The operation needs a complete Boolean
algebra, which the domain of every conjoinable type is, since such a type ends in `t`.

## References

* [partee-rooth-1983]
-/

@[expose] public section

namespace Coordinator

variable {α : Type*} [CompleteBooleanAlgebra α] {c : Coordinator}

/-- On a set of coordinands a coordinator denotes their infimum if it is conjunctive or
adversative, their supremum if it is disjunctive, and the complement of their supremum if it is
negative. -/
def denote (c : Coordinator) : Set α → α :=
  match c.role with
  | .conjunctive | .adversative => sInf
  | .disjunctive => sSup
  | .negative => fun s ↦ (sSup s)ᶜ

theorem denote_of_conjunctive (h : c.role = .conjunctive) (s : Set α) : c.denote s = sInf s := by
  simp [denote, h]

theorem denote_of_disjunctive (h : c.role = .disjunctive) (s : Set α) : c.denote s = sSup s := by
  simp [denote, h]

theorem denote_of_negative (h : c.role = .negative) (s : Set α) : c.denote s = (sSup s)ᶜ := by
  simp [denote, h]

theorem denote_of_adversative (h : c.role = .adversative) (s : Set α) : c.denote s = sInf s := by
  simp [denote, h]

/-- Coordinating a constituent alone returns it, except under negative coordination. -/
theorem denote_singleton (hc : c.role ≠ .negative) (p : α) : c.denote {p} = p := by
  rcases h : c.role <;> simp_all [denote]

/-- Coordinating a constituent with itself returns it, except under negative coordination. -/
theorem denote_pair_self (hc : c.role ≠ .negative) (p : α) : c.denote {p, p} = p := by
  rw [Set.pair_eq_singleton, denote_singleton hc]

/-- The coordination of functions is computed pointwise. -/
theorem denote_apply {ι : Type*} (c : Coordinator) (s : Set (ι → α)) (i : ι) :
    c.denote s i = c.denote ((· i) '' s) := by
  rcases h : c.role <;> simp [denote, h, sSup_apply, sInf_apply, sSup_image', sInf_image']

end Coordinator
