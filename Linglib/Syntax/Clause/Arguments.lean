module

public import Linglib.Semantics.ArgumentStructure.Valency
public import Mathlib.Logic.Function.DependsOn

/-!
# Core arguments of a clause token

This file defines `Clause.Arguments α`, the assignment of an `α`, such as a DP, its φ-features or
its number, to each core-argument position of a clause token, with `none` at an unfilled position.
The filled positions are the clause's valency, which fixes the comparative role of each argument.
A property of clause tokens is a function out of `Arguments α`; that it is local to some positions
is mathlib's `DependsOn`, and a role conditions it when replacing the argument bearing that role
can change it. A property local to some positions is conditioned only at them.

## Main definitions

* `Clause.Arguments`, with the shapes `unaccusative`, `unergative`, `transitive` and `empty`.
* `Clause.Arguments.valency`: the filled positions.
* `Clause.Arguments.Conditions`: the roles whose argument conditions a property of clauses.

## Main results

* `Clause.Arguments.mem_of_dependsOn`: a local property is conditioned only at its positions.

## References

* [harley-2014]
-/

@[expose] public section

namespace Clause

open ArgumentStructure Function

/-- What each core-argument position of a clause token bears, `none` where the
position is unfilled. -/
abbrev Arguments (α : Type*) := ArgPosition → Option α

namespace Arguments

variable {α β : Type*} (x obj subj : α)

/-- An intransitive clause whose sole argument is internal. -/
def unaccusative : Arguments α
  | .internal => some x
  | .external => none

/-- An intransitive clause whose sole argument is external. -/
def unergative : Arguments α
  | .internal => none
  | .external => some x

/-- A transitive clause: an internal argument `obj` and an external one
`subj`. -/
def transitive : Arguments α
  | .internal => some obj
  | .external => some subj

/-- A clause with no core argument filled. -/
def empty : Arguments α := fun _ ↦ none

/-- The filled positions. -/
def valency (c : Arguments α) : Valency := ({p | (c p).isSome} : Finset ArgPosition)

@[simp] theorem mem_valency {c : Arguments α} {p : ArgPosition} :
    p ∈ c.valency ↔ (c p).isSome := by
  simp [valency]

@[simp] theorem valency_unaccusative : (unaccusative x).valency = {.internal} := by
  ext p; cases p <;> simp [unaccusative]

@[simp] theorem valency_unergative : (unergative x).valency = {.external} := by
  ext p; cases p <;> simp [unergative]

@[simp] theorem valency_transitive : (transitive obj subj).valency = {.internal, .external} := by
  ext p; cases p <;> simp [transitive]

@[simp] theorem valency_empty : (empty : Arguments α).valency = ∅ := by
  ext p; simp [empty]

/-! ### Conditioning -/

/-- The argument bearing role `r` conditions the property `F` of clause tokens: in some clause,
replacing that argument alone changes `F`. -/
def Conditions (F : Arguments α → β) (r : ArgumentRole) : Prop :=
  ∃ (c : Arguments α) (p : ArgPosition), c.valency.role p = some r ∧
    ∃ x y : α, F (update c p (some x)) ≠ F (update c p (some y))

/-- A property depending on the positions `s` alone is conditioned only at them: in a clause
where replacing the argument at `p` changes it, `p ∈ s`. -/
theorem mem_of_dependsOn {F : Arguments α → β} {s : Set ArgPosition} (hF : DependsOn F s)
    {c : Arguments α} {p : ArgPosition} {x y : α}
    (h : F (update c p (some x)) ≠ F (update c p (some y))) : p ∈ s := by
  by_contra hp
  refine h (hF fun i hi ↦ ?_)
  rw [update_of_ne (ne_of_mem_of_not_mem hi hp), update_of_ne (ne_of_mem_of_not_mem hi hp)]

end Arguments

end Clause
