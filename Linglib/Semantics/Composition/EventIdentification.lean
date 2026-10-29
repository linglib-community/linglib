module

public import Linglib.Semantics.Modification.Basic

/-!
# Event identification

*Event identification* is Kratzer's rule for adding an argument-introducing head to a predicate
of events: the head's relation between individuals and events and the predicate's set of events
combine by conjunction at the event, leaving the individual open. It is
[meet with the predicate lifted to a relation](##eventIdentification_eq_inf), the relational
counterpart of predicate modification, and
[two applications conjoin their predicates](##eventIdentification_eventIdentification).

## Main definitions

* `ArgumentStructure.eventIdentification`: the combination of a relation and a predicate.

## Implementation notes

Kratzer's rule is partial: it is undefined when the two inputs restrict the event to disjoint
sorts, actions and states. Here it is total, and such inputs
[yield the empty relation](##eventIdentification_eq_bot_iff). The carrier is any pair of types,
so that the type-driven composition engine, whose eventualities are a sort of their own beside
the individuals, uses the same operation.

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
