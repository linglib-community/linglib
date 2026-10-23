module

public import Linglib.Semantics.ArgumentStructure.Valency

/-!
# Core arguments of a clause token

`Clause.Arguments α` assigns an `α`, such as a DP, its φ-features or its number, to each
core-argument position of a clause token (`ArgumentStructure.ArgPosition`), with `none` at an
unfilled position. The filled positions are the clause's valency, off which
`ArgumentStructure.Valency.role` reads their comparative roles.

## Main definitions

* `Clause.Arguments`: the assignment of an `α` to each filled position.
* `Clause.Arguments.unaccusative`, `unergative`, `transitive`, `empty`: the clause shapes.
* `Clause.Arguments.valency`: the filled positions.

## Main results

* `Clause.Arguments.unaccusative_isRootValency`, `unergative_isVoiceValency`,
  `transitive_isTransitive`: the shapes land in the valency classes of Coon's division of labor.

## References

* [coon-2019]
-/

@[expose] public section

namespace Clause

open ArgumentStructure

/-- What each core-argument position of a clause token bears, `none` where the
position is unfilled. -/
abbrev Arguments (α : Type*) := ArgPosition → Option α

namespace Arguments

variable {α : Type*} (x obj subj : α)

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
def valency (c : Arguments α) : Valency := Finset.univ.filter fun p ↦ (c p).isSome

@[simp] theorem valency_unaccusative : (unaccusative x).valency = {.internal} := by
  ext p; cases p <;> simp [valency, unaccusative]

@[simp] theorem valency_unergative : (unergative x).valency = {.external} := by
  ext p; cases p <;> simp [valency, unergative]

@[simp] theorem valency_transitive : (transitive obj subj).valency = {.internal, .external} := by
  ext p; cases p <;> simp [valency, transitive]

@[simp] theorem valency_empty : (empty : Arguments α).valency = ∅ := by
  ext p; simp [valency, empty]

theorem unaccusative_isRootValency : (unaccusative x).valency.IsRootValency := by
  rw [valency_unaccusative]; exact le_rfl

theorem unergative_isVoiceValency : (unergative x).valency.IsVoiceValency := by
  rw [valency_unergative]; exact le_rfl

theorem transitive_isTransitive : (transitive obj subj).valency.IsTransitive :=
  valency_transitive obj subj

end Arguments

end Clause
