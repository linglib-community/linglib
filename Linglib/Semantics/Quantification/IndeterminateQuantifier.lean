module

public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Syntax.Category.Determiner.IndeterminateQuantifier

/-!
# The reading of an indeterminate quantifier

An indeterminate quantifier applies its particle's coordination to the values its scope takes on
the restrictor, as Kratzer and Shimoyama propose for Japanese. A disjunctive particle takes the
supremum, so the quantifier is `Quantifier.Det.some`; a conjunctive particle takes the infimum,
`every`; and a negative particle the complement of the supremum, `no`.

## Main definitions

* `IndeterminateQuantifier.reading`: the particle's coordination over the restrictor.

## Main statements

* `IndeterminateQuantifier.reading_of_disjunctive`,
  `IndeterminateQuantifier.reading_of_conjunctive`,
  `IndeterminateQuantifier.reading_of_negative`: the readings are `some`, `every` and `no`.

## References

* [kratzer-shimoyama-2002]
* [shimoyama-2006]
-/

@[expose] public section

namespace IndeterminateQuantifier

open Quantifier

universe u

variable (q : IndeterminateQuantifier)

/-- The reading of an indeterminate quantifier applies its particle's coordination to the
values the scope takes on the restrictor. -/
def reading : Det.Family.{u} :=
  fun _ _ A B ↦ q.particle.denote ((· ∈ B) '' A)

/-- An indeterminate quantifier denotes its reading. -/
instance : Denotes IndeterminateQuantifier (Set Det.Family.{u}) where
  denote q := {q.reading}

variable {q}

/-- Under a disjunctive particle the reading is `Quantifier.Det.some`. -/
theorem reading_of_disjunctive (h : q.particle.role = .disjunctive) :
    q.reading = Det.Family.some.{u} := by
  funext _ _ A B
  rw [reading, Coordinator.denote_of_disjunctive h, ← Det.some_eq_sSup_image]; rfl

/-- Under a conjunctive particle the reading is `every`. -/
theorem reading_of_conjunctive (h : q.particle.role = .conjunctive) :
    q.reading = Det.Family.every.{u} := by
  funext _ _ A B
  rw [reading, Coordinator.denote_of_conjunctive h, ← Det.every_eq_sInf_image]; rfl

/-- Under a negative particle the reading is `no`. -/
theorem reading_of_negative (h : q.particle.role = .negative) :
    q.reading = Det.Family.no.{u} := by
  funext _ _ A B
  rw [reading, Coordinator.denote_of_negative h, ← Det.no_eq_compl_sSup_image]; rfl

end IndeterminateQuantifier
