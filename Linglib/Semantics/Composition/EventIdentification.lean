module

public import Linglib.Semantics.Modification.Basic

/-!
# Event Identification

This file defines Event Identification, the composition principle by which Kratzer adds an
argument-introducing head to a predicate of events. The head denotes a relation between
individuals and events, the predicate a set of events, and the two combine by conjunction at the
event, leaving the individual argument open: an agent head and *feed the dog* yield the relation
that holds of an individual and an event when the individual is the agent of the event and the
event is a feeding of the dog. Event Identification is meet with the predicate lifted to a
relation constant in the individual, so it is the relational counterpart of predicate
modification, and repeated applications chain conditions on the same event.

## Main definitions

* `ArgumentStructure.eventIdentification`: the combination of a relation and a predicate.

## Main results

* `eventIdentification_eq_inf`, `eventIdentification_eq_comp`: Event Identification is meet
  with the lifted predicate, and predicate modification of each section of the relation.
* `eventIdentification_eventIdentification`: two applications conjoin the predicates.
* `eventIdentification_eq_bot_iff`: the result is empty exactly when, for every individual, the
  relation's events and the predicate's are disjoint.

## Implementation notes

Kratzer's rule is partial: it is undefined when the two inputs restrict the event to disjoint
sorts, actions and states. Here it is total, and such inputs yield the empty relation
(`eventIdentification_eq_bot_iff`). The carrier is any pair of types, so that the type-driven
composition engine, whose events share the domain of individuals, uses the same operation.

## References

* [kratzer-1996]
-/

@[expose] public section

namespace ArgumentStructure

variable {α β : Type*}

/-- Event Identification conjoins the relation `f` and the predicate `g` at the event, leaving
the individual argument open. -/
def eventIdentification (f : α → β → Prop) (g : β → Prop) : α → β → Prop :=
  fun x e ↦ f x e ∧ g e

variable {f f' : α → β → Prop} {g g' : β → Prop}

@[simp]
theorem eventIdentification_apply (x : α) (e : β) :
    eventIdentification f g x e ↔ f x e ∧ g e :=
  Iff.rfl

theorem eventIdentification_eq_inf : eventIdentification f g = f ⊓ Function.const α g :=
  rfl

/-- Event Identification is predicate modification of each of the relation's sections. -/
theorem eventIdentification_eq_comp :
    eventIdentification f g = Modifier.intersective g ∘ f := by
  ext
  simp [and_comm]

theorem eventIdentification_mono (hf : f ≤ f') (hg : g ≤ g') :
    eventIdentification f g ≤ eventIdentification f' g' :=
  fun x e h ↦ ⟨hf x e h.1, hg e h.2⟩

theorem eventIdentification_eventIdentification (h : β → Prop) :
    eventIdentification (eventIdentification f g) h = eventIdentification f (g ⊓ h) := by
  ext
  simp [and_assoc]

theorem eventIdentification_eq_bot_iff :
    eventIdentification f g = ⊥ ↔ ∀ x, Disjoint (f x) g := by
  simp [funext_iff, Pi.disjoint_iff]

end ArgumentStructure
