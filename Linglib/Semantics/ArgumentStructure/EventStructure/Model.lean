module

public import Linglib.Logic.Modal.Defs

/-!
# Models of the event-structure primitives

Event-structural decomposition builds the meaning of a verb from two relations: an eventuality
`e` *gives rise to* a state `s`, written `e ~[become] s`, and an eventuality `v` *causes* an
eventuality `e`, written `v ~[cause] e`. An `EventStructure.Model` over types of states and
eventualities is a choice of these relations, with a third, `causeState`, between an eventuality
and a state it causes without a change, for a causative head over a stative complement.

The verbal heads are possibility along the relations. For a state predicate `p`, the
change-of-state head yields `◇[become] p`, the eventualities that give rise to a `p`-state, and
for a predicate `q` of eventualities the causative head yields `◇[cause] q`, the eventualities
that cause a `q`-eventuality. A causative of a change of state is `◇[cause] (◇[become] p)`.

## Implementation notes

The sorts are type parameters, so a relation cannot be applied to an argument of the wrong sort.
An analysis on which states and events are sorts of one domain of eventualities takes the two
types to be the same.

A model has no relation between individuals and eventualities and no predicates. The causative
head of [beavers-koontz-garboden-2020] also makes its subject the effector of the causing
eventuality; that is a thematic relation, which a caller supplies and states as a conjunct
(`Template.denote`), so that the same relations serve analyses on which the causer is an agent or
is introduced by a separate head. The predicates are those of a root.

`become` runs from the eventuality to the state it gives rise to, the direction of `cause`, so
that the two compose; [beavers-koontz-garboden-2020] write the state first.

Causation of a state is a field of its own and not `cause` followed by `become`, since a state
that is caused need not arise from a change: [yu-ausensi-smith-2023] let the causative head take
a caused eventuality of either sort. It defaults to the empty relation, for an analysis on which
every caused state is the result of a change.

## References

* [beavers-koontz-garboden-2020]
* [yu-ausensi-smith-2023]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

/-- A model of the event-structure primitives, the relations that the verbal heads introduce. -/
@[ext]
structure Model (State Event : Type*) where
  /-- An eventuality and a state it gives rise to. -/
  become : SetRel Event State
  /-- An eventuality and an eventuality it causes. -/
  cause : SetRel Event Event
  /-- An eventuality and a state it causes without a change. -/
  causeState : SetRel Event State := ∅

namespace Model

open ModalLogic
open scoped SetRel

/-- Models are ordered by inclusion of their relations. -/
instance {State Event : Type*} : PartialOrder (Model State Event) :=
  PartialOrder.lift (fun M ↦ (M.become, M.cause, M.causeState)) fun _ _ h ↦
    Model.ext (congrArg Prod.fst h) (congrArg (fun p ↦ p.2.1) h)
      (congrArg (fun p ↦ p.2.2) h)

theorem le_def {State Event : Type*} {M N : Model State Event} :
    M ≤ N ↔ M.become ⊆ N.become ∧ M.cause ⊆ N.cause ∧ M.causeState ⊆ N.causeState := Iff.rfl

end Model

end ArgumentStructure.EventStructure
