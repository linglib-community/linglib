module

public import Linglib.Syntax.Category.Coordinator

/-!
# English coordinators

English coordinates with free words that stand before the second coordinand: *and*, *or*, *but*
and, after a negative, *nor*. The emphatic constructions pair a distinct first word with the
plain coordinator: *both … and*, *either … or*, *neither … nor*.

## Main definitions

* `English.Coordination.and_`, `English.Coordination.or_`, `English.Coordination.but_`,
  `English.Coordination.nor_`: the conjunctive, disjunctive, adversative and negative
  coordinators.
* `English.Coordination.bothAnd`, `English.Coordination.eitherOr`,
  `English.Coordination.neitherNor`: the emphatic constructions.

## References

* [haspelmath-2007]
-/

@[expose] public section

namespace English.Coordination

/-- *and*. -/
def and_ : Coordinator :=
  { morph := .free "and", gloss := "and", role := .conjunctive }

/-- *or*. -/
def or_ : Coordinator :=
  { morph := .free "or", gloss := "or", role := .disjunctive }

/-- *but*. -/
def but_ : Coordinator :=
  { morph := .free "but", gloss := "but", role := .adversative }

/-- *nor*. -/
def nor_ : Coordinator :=
  { morph := .free "nor", gloss := "nor", role := .negative }

/-- *both … and*. -/
def bothAnd : Coordinator.Correlative := ⟨[.free "both"], [and_.morph], and_⟩

/-- *either … or*. -/
def eitherOr : Coordinator.Correlative := ⟨[.free "either"], [or_.morph], or_⟩

/-- *neither … nor*. -/
def neitherNor : Coordinator.Correlative := ⟨[.free "neither"], [nor_.morph], nor_⟩

end English.Coordination
