module

public import Linglib.Semantics.Modality.Content

/-!
# Event-relative modality

An event-relative modal has an accessibility relation from events to worlds, and its event
variable is bound by [the closest binder above it](##Modality.ModalPosition.binder): aspect,
which binds the event the verb phrase describes, for a low modal below aspect, and the speech
event or an attitude event for a high modal above tense. Speech and attitude events have
propositional content, so an epistemic modal bound by one of them is necessity or possibility
along `Modality.compatible`, and one bound by an event without content has no domain.

## References

* [hacquard-2006]
* [hacquard-2010]
-/

@[expose] public section

namespace Modality

/-- The events a modal's event variable can be bound to. -/
inductive EventBinder
  /-- The speech event, bound by the default binder at the top of a matrix clause. -/
  | speechAct
  /-- The event of an attitude verb whose complement contains the modal. -/
  | attitude
  /-- The event the verb phrase describes, bound by aspect. -/
  | vpEvent
  deriving DecidableEq, Repr

/-- The two positions of a modal in its clause. -/
inductive ModalPosition
  /-- Right above tense, out of reach of the clause's aspect. -/
  | high
  /-- Right above the verb phrase, below aspect. -/
  | low
  deriving DecidableEq, Repr

/-- The closest binder above a modal is the clause's aspect, binding the event the verb phrase
describes, for a low modal, and for a high modal the binder above the clause, which anchors it to
the event `outer`: the speech event in a matrix clause, and in a complement the event of the
embedding verb, which the matrix aspect binds. -/
def ModalPosition.binder : ModalPosition → EventBinder → EventBinder
  | high, outer => outer
  | low, _ => .vpEvent

end Modality
