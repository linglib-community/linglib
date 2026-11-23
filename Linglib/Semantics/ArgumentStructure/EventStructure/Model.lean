module

public import Linglib.Logic.Modal.Defs

/-!
# Models of the event-structure primitives

This file defines the models in which event structure templates are interpreted. An
`EventStructure.Model` over a type of states and a type of events consists of three relations:

* `become`, between an event and a state it gives rise to;
* `cause`, between an event and an event it causes;
* `causeState`, between an event and a state it causes without a change.

The verbal heads are possibility along these relations: `◇[become] p` holds of the events that
give rise to a `p`-state, and `◇[cause] q` of the events that cause a `q`-event. Models are
ordered by inclusion of their relations.

## Implementation notes

* States and events are separate type parameters, so a relation cannot be applied at the wrong
  sort. An analysis with one domain of eventualities takes the two types to be the same.
* A model has no relation between individuals and events and no predicates. `Template.denote`
  takes the thematic relation and the predicates of a root as arguments.
* `become` runs from the event to the state, the direction of `cause`, so that the two compose.
* `causeState` is a field of its own and not `cause` followed by `become`, because a caused state
  need not arise from a change ([yu-ausensi-smith-2023]). It defaults to the empty relation.

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
