module

public import Linglib.Logic.Modal.Defs

/-!
# Event-relative modality

An event-relative modal has an accessibility relation from events to worlds, and its event
variable is bound by [the closest binder above it](##Modality.ModalPosition.binder): aspect,
which binds the event the verb phrase describes, for a modal below aspect, and the speech event
or an attitude event for a modal above it. Speech and attitude events have propositional content,
given by a content function `con : E → Option (Set W)` that is undefined at an event without
content. The epistemic relation `contentAccessible con` relates an event to the worlds compatible
with its content, and epistemic necessity and possibility are `□` and `◇` along it, [universal and
existential over the content](##Modality.box_contentAccessible_iff).

## Implementation notes

An epistemic modal anchored to an event without content has an undefined domain. The relation
relates such an event to no world, so possibility over it is false and necessity vacuously true.

## References

* [hacquard-2006]
* [hacquard-2010]
-/

@[expose] public section

namespace Modality

open ModalLogic
open scoped SetRel

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
  | aboveAsp
  /-- Right above the verb phrase, below aspect. -/
  | belowAsp
  deriving DecidableEq, Repr

/-- The closest binder above a modal is aspect, binding the event the verb phrase describes, for
a modal below aspect, and for a modal above aspect the event `outer` the clause is anchored to:
the speech event in a matrix clause, the attitude event in the complement of an attitude verb. -/
def ModalPosition.binder : ModalPosition → EventBinder → EventBinder
  | aboveAsp, outer => outer
  | belowAsp, _ => .vpEvent

/-! ### The epistemic accessibility relation -/

variable {E W : Type*} {con : E → Option (Set W)} {e : E} {C : Set W} {w : W} {q : W → Prop}

/-- The epistemic accessibility relation of a content function relates an event to the worlds
compatible with its content, and an event without content to no world. -/
def contentAccessible (con : E → Option (Set W)) : SetRel E W :=
  .ofSuccessors fun e ↦ (con e).getD ∅

@[simp]
theorem mem_contentAccessible : e ~[contentAccessible con] w ↔ ∃ C ∈ con e, w ∈ C := by
  cases h : con e <;> simp [contentAccessible, h]

theorem mem_contentAccessible_of_eq_some (h : con e = some C) :
    e ~[contentAccessible con] w ↔ w ∈ C := by
  simp [h]

theorem box_contentAccessible_iff (h : con e = some C) :
    □[contentAccessible con] q e ↔ ∀ w ∈ C, q w :=
  forall_congr' fun _ ↦ imp_congr_left (mem_contentAccessible_of_eq_some h)

theorem diamond_contentAccessible_iff (h : con e = some C) :
    ◇[contentAccessible con] q e ↔ ∃ w ∈ C, q w :=
  exists_congr fun _ ↦ and_congr_left' (mem_contentAccessible_of_eq_some h)

theorem not_diamond_contentAccessible (h : con e = none) : ¬ ◇[contentAccessible con] q e :=
  fun ⟨_, hw, _⟩ ↦ by simp [h] at hw

end Modality
