module

public import Mathlib.Data.Set.Basic

/-!
# Event-relative modality

This file defines the binders of a modal's event variable and quantification over the content
of an event, the two ingredients of Hacquard's event-relative semantics for modals. In that
semantics a modal's domain is projected from an event rather than fixed by the context of
utterance. The modal's event variable is bound by the closest binder
above it: aspect binds a modal below AspP to the event the verb phrase describes, and a modal
above AspP is bound to the speech event in a matrix clause and to the attitude event in the
complement of an attitude verb. Speech and attitude events have propositional content, the set
of worlds compatible with what is asserted or believed, and a modal anchored to such an event
can quantify over that content. Content is a property of the event and not of its binder: most
verb phrases describe events without content, but an aspect-bound modal over an attitude
predicate is anchored to a contentful event and again has a reading over its content.

## Main definitions

* `Modality.EventBinder`: the three events a modal's event variable can be bound to.
* `Modality.ModalPosition`: the position of a modal relative to aspect, with the binders
  `ModalPosition.matrixBinder` and `ModalPosition.embeddedBinder` that position determines.
* `Modality.contentNecessity`, `Modality.contentPossibility`: quantification over the content of
  the anchoring event, undefined (false) when the event has none.

## Main statements

* `Modality.contentNecessity_const`, `Modality.contentPossibility_const`: over a proposition
  that does not vary with the world, the quantifier contributes only the consistency of the
  content. A modal anchored to the event that embeds it is therefore vacuous.

## Implementation notes

The content of an event is a function `con : E → Option (Set W)`, the worlds compatible with
the event's content where it has one. Ordering sources play no role in content licensing and
are left to `Semantics/Modality/Necessity`, whose operators apply to a base `f e` projected from
an event as they do to any other.

## References

* [hacquard-2006]
* [hacquard-2010]
-/

@[expose] public section

namespace Modality

/-- The events a modal's event variable can be bound to. -/
inductive EventBinder
  /-- The speech event, bound at the edge of a matrix clause. -/
  | speechAct
  /-- The event of an attitude verb, bound at the edge of its complement. -/
  | attitude
  /-- The event the verb phrase describes, bound by aspect. -/
  | vpEvent
  deriving DecidableEq, Repr

/-- The position of a modal relative to aspect. -/
inductive ModalPosition
  | aboveAsp
  | belowAsp
  deriving DecidableEq, Repr

namespace ModalPosition

/-- The closest binder above a modal in a matrix clause is aspect below AspP and the speech act
above it. -/
def matrixBinder : ModalPosition → EventBinder
  | aboveAsp => .speechAct
  | belowAsp => .vpEvent

/-- The closest binder above a modal in the complement of an attitude verb is aspect below AspP
and the attitude verb above it. -/
def embeddedBinder : ModalPosition → EventBinder
  | aboveAsp => .attitude
  | belowAsp => .vpEvent

@[simp]
theorem embeddedBinder_belowAsp : belowAsp.embeddedBinder = belowAsp.matrixBinder := rfl

theorem matrixBinder_eq_vpEvent {pos : ModalPosition} :
    pos.matrixBinder = .vpEvent ↔ pos = belowAsp := by
  cases pos <;> simp [matrixBinder]

theorem embeddedBinder_eq_vpEvent {pos : ModalPosition} :
    pos.embeddedBinder = .vpEvent ↔ pos = belowAsp := by
  cases pos <;> simp [embeddedBinder]

end ModalPosition

/-! ### Quantification over the content of an event -/

variable {E W : Type*} {con : E → Option (Set W)} {p q : W → Prop} {r : Prop} {e : E}
  {C : Set W}

/-- Necessity over the content of the anchoring event holds when the event has content and the
proposition holds throughout it. -/
def contentNecessity (con : E → Option (Set W)) (q : W → Prop) (e : E) : Prop :=
  ∃ C ∈ con e, ∀ w ∈ C, q w

/-- Possibility over the content of the anchoring event holds when the event has content and
the proposition holds somewhere in it. -/
def contentPossibility (con : E → Option (Set W)) (q : W → Prop) (e : E) : Prop :=
  ∃ C ∈ con e, ∃ w ∈ C, q w

theorem contentNecessity_iff_of_eq_some (h : con e = some C) :
    contentNecessity con q e ↔ ∀ w ∈ C, q w := by
  simp [contentNecessity, h]

theorem contentPossibility_iff_of_eq_some (h : con e = some C) :
    contentPossibility con q e ↔ ∃ w ∈ C, q w := by
  simp [contentPossibility, h]

theorem isSome_of_contentNecessity (h : contentNecessity con q e) : (con e).isSome :=
  let ⟨_, hC, _⟩ := h
  Option.isSome_of_mem hC

theorem isSome_of_contentPossibility (h : contentPossibility con q e) : (con e).isSome :=
  let ⟨_, hC, _⟩ := h
  Option.isSome_of_mem hC

theorem not_contentNecessity_of_eq_none (h : con e = none) : ¬ contentNecessity con q e := by
  simp [contentNecessity, h]

theorem not_contentPossibility_of_eq_none (h : con e = none) : ¬ contentPossibility con q e := by
  simp [contentPossibility, h]

theorem contentNecessity.mono (hpq : ∀ w, p w → q w) (h : contentNecessity con p e) :
    contentNecessity con q e :=
  let ⟨C, hC, hp⟩ := h
  ⟨C, hC, fun w hw ↦ hpq w (hp w hw)⟩

theorem contentPossibility.mono (hpq : ∀ w, p w → q w) (h : contentPossibility con p e) :
    contentPossibility con q e :=
  let ⟨C, hC, w, hw, hp⟩ := h
  ⟨C, hC, w, hw, hpq w hp⟩

/-- Necessity over a consistent content entails possibility. -/
theorem contentNecessity.contentPossibility (hC : con e = some C) (hne : C.Nonempty)
    (h : contentNecessity con q e) : contentPossibility con q e :=
  let ⟨w, hw⟩ := hne
  (contentPossibility_iff_of_eq_some hC).2 ⟨w, hw, (contentNecessity_iff_of_eq_some hC).1 h w hw⟩

theorem contentPossibility_iff_not_contentNecessity_not (hC : con e = some C) :
    contentPossibility con q e ↔ ¬ contentNecessity con (fun w ↦ ¬ q w) e := by
  simp [contentPossibility_iff_of_eq_some hC, contentNecessity_iff_of_eq_some hC]

/-- Necessity of a proposition that does not vary with the world holds when the content is
inconsistent or the proposition is true. -/
theorem contentNecessity_const (hC : con e = some C) :
    contentNecessity con (fun _ ↦ r) e ↔ (C.Nonempty → r) := by
  simp [contentNecessity_iff_of_eq_some hC, Set.Nonempty]

/-- Possibility of a proposition that does not vary with the world holds when the content is
consistent and the proposition is true. -/
theorem contentPossibility_const (hC : con e = some C) :
    contentPossibility con (fun _ ↦ r) e ↔ C.Nonempty ∧ r := by
  simp [contentPossibility_iff_of_eq_some hC, Set.Nonempty]

theorem contentNecessity_contentNecessity :
    contentNecessity con (fun _ ↦ contentNecessity con q e) e ↔ contentNecessity con q e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.imp fun _ hC ↦ ⟨hC.1, fun _ _ ↦ h⟩⟩
  obtain ⟨C, hC, hall⟩ := h
  rcases C.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  exacts [⟨∅, hC, fun _ hw ↦ hw.elim⟩, hall w hw]

theorem contentPossibility_contentNecessity :
    contentPossibility con (fun _ ↦ contentNecessity con q e) e ↔
      ∃ C ∈ con e, C.Nonempty ∧ ∀ w ∈ C, q w :=
  ⟨fun ⟨C, hC, w, hw, h⟩ ↦ ⟨C, hC, ⟨w, hw⟩, (contentNecessity_iff_of_eq_some hC).1 h⟩,
    fun ⟨C, hC, ⟨w, hw⟩, h⟩ ↦ ⟨C, hC, w, hw, C, hC, h⟩⟩

end Modality
