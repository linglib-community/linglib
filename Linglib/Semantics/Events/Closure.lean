/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Closure of the eventuality argument

A clause denotes a world-indexed predicate of eventualities until some head closes the
eventuality argument existentially. Accounts of complement choice differ on the head:
[grano-2024] makes it mood, the indicative closing the argument and one subjunctive passing it
up, while [fusco-sgrizzi-2026] make it a head that a clause-sized infinitive contains and a
smaller one lacks. They agree on why it matters. The content of an intention is causally
self-referential ([searle-1983], [harman-1976]): it is satisfied only by an eventuality that the
intention itself brings about. Such content closes the argument over the eventualities the
attitude state causes, which needs the open predicate and cannot be computed from the closed
proposition.

## Main declarations

* `Event.closure`: existential closure of the eventuality argument.
* `Event.causedClosure`: closure over the eventualities a given state causes, the causally
  self-referential prejacent.

## Main statements

* `Event.causedClosure_factorsThrough_iff`: the causally self-referential prejacent is a function
  of the closed proposition exactly when causation by the state is trivial at every world,
  relating the state to every eventuality or to none.

## Implementation notes

Causation is a relation between two eventualities at each world, the papers' `cause s e w`. For a
fixed world `causedClosure` is possibility along the causal relation of that world, as the
causative head `ArgumentStructure.EventStructure.Interpretation.vCause` is possibility along
`cause`.

## References

* [grano-2024]
* [fusco-sgrizzi-2026]
* [searle-1983]
* [harman-1976]
-/

@[expose] public section

namespace Event

open ModalLogic
open scoped SetRel

variable {Ev W : Type*} {cause cause' : W → SetRel Ev Ev} {s : Ev} {P Q : W → Ev → Prop} {w : W}

/-- Existential closure of a clause's eventuality argument, yielding a proposition. -/
def closure (P : W → Ev → Prop) (w : W) : Prop := ∃ e, P w e

/-- Closure of a clause's eventuality argument over the eventualities that the state `s` causes,
the causally self-referential prejacent of an intention ([searle-1983]). -/
def causedClosure (cause : W → SetRel Ev Ev) (s : Ev) (P : W → Ev → Prop) (w : W) : Prop :=
  ◇[cause w] (P w) s

theorem closure_mono (h : ∀ e, P w e → Q w e) : closure P w → closure Q w :=
  Exists.imp h

theorem causedClosure_mono (h : ∀ e, s ~[cause w] e → P w e → Q w e) :
    causedClosure cause s P w → causedClosure cause s Q w :=
  Exists.imp fun e he ↦ ⟨he.1, h e he.1 he.2⟩

theorem causedClosure_mono_left (h : ∀ e, s ~[cause w] e → s ~[cause' w] e) :
    causedClosure cause s P w → causedClosure cause' s P w :=
  Exists.imp fun e he ↦ ⟨h e he.1, he.2⟩

/-- The causally self-referential prejacent entails the closed proposition. -/
theorem causedClosure.closure (h : causedClosure cause s P w) : closure P w :=
  h.imp fun _ he ↦ he.2

theorem causedClosure_iff_of_forall (h : ∀ e, s ~[cause w] e) :
    causedClosure cause s P w ↔ closure P w :=
  exists_congr fun e ↦ and_iff_right (h e)

theorem not_causedClosure_of_forall_not (h : ∀ e, ¬ s ~[cause w] e) :
    ¬ causedClosure cause s P w :=
  fun ⟨e, he, _⟩ ↦ h e he

/-- Causal self-reference needs the open eventuality argument. The prejacent is a function of the
closed proposition exactly when causation by the state is trivial at every world, relating the
state to every eventuality or to none. -/
theorem causedClosure_factorsThrough_iff :
    (causedClosure cause s).FactorsThrough closure ↔
      ∀ w, (∀ e, s ~[cause w] e) ∨ ∀ e, ¬ s ~[cause w] e := by
  refine ⟨fun h w ↦ ?_, fun h P Q hPQ ↦ funext fun w ↦ propext ?_⟩
  · by_contra hw
    obtain ⟨⟨e₂, h₂⟩, e₁, h₁⟩ := not_or.1 hw |>.imp not_forall.1 not_forall.1
    have key := congrFun (@h (fun _ e ↦ e = e₁) (fun _ e ↦ e = e₂)
      (funext fun _ ↦ propext ⟨fun _ ↦ ⟨e₂, rfl⟩, fun _ ↦ ⟨e₁, rfl⟩⟩)) w
    obtain ⟨e, he, rfl⟩ := key.mp ⟨e₁, not_not.1 h₁, rfl⟩
    exact h₂ he
  · rcases h w with hw | hw
    · rw [causedClosure_iff_of_forall hw, causedClosure_iff_of_forall hw, hPQ]
    · exact iff_of_false (not_causedClosure_of_forall_not hw) (not_causedClosure_of_forall_not hw)

end Event
