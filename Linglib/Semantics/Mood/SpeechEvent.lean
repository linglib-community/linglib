/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Mood.Context
public import Linglib.Semantics.Modality.Basic

/-!
# The speech event and its content

Hacquard adopts the Speech Act Phrase of Speas and Tenny, whose head introduces a speech event
`e*` and encodes illocutionary force, and adds that the speech event has content `CON(e*)`: the
speaker's beliefs for a declarative, the addressee's To-Do List for an imperative. A modal bound
by `e*` reads `CON(e*)` as its conversational background, so the event rather than a lexical
ambiguity supplies the modal's flavor. Here `CON(e*)` enters the discourse context through the
update of the force, which changes the speaker's context set for a declarative and the addressee's
ordering for an imperative, and the licensed modal and flavor are read off the component the force
updates, in the states of the participants it updates.

## Main definitions

* `Mood.SpeechEvent`: a force together with `CON(e*)`.
* `Mood.SpeechEvent.toContext`, `Mood.SpeechEvent.modal`: the induced discourse context and its
  modal.
* `Discourse.SpeechAct.Force.primaryFlavor`: Hacquard's flavor of a speech act, read off its
  component.

## Implementation notes

* Hacquard's four speech acts are declaratives, interrogatives, imperatives and quotatives, after
  Tenny and Speas; Speas and Tenny 2003 derive the subjunctive in place of the quotative, whose
  status they leave open. `Discourse.SpeechAct.Force` has neither the subjunctive nor the
  quotative and adds the promise and the exclamation.
* Hacquard gives content only to declaratives and imperatives, and the inquiry licenses no
  flavor.
* Hacquard's deontic accessibility relation reads the To-Do List of the addressee of whatever event
  binds the modal, a declarative speech event included, and keeps the worlds compatible with it.
  Here the To-Do List is the content of an imperative speech event and ranks the worlds instead;
  the optimal worlds are the compatible ones whenever the list is consistent.
* Which event binds a modal is the business of `Semantics/Modality/EventRelativity.lean`.

## References

* [hacquard-2006]
* [speas-tenny-2003]
* [portner-2004]
* [portner-2018]
* [zanuttini-pak-portner-2012]
* [kratzer-1981]
-/

@[expose] public section

namespace Mood

open DynamicSemantics
open Modality (ModalFlavor)
open Discourse (Role)
open Discourse.SpeechAct (Force)

variable {W : Type*}

/-! ### Speech events -/

/-- A speech act event `e*` with its content `CON(e*)` ([hacquard-2006], her assumption 4,
p. 144). -/
structure SpeechEvent (W : Type*) where
  /-- The illocutionary force the SAP head encodes. -/
  force : Force
  /-- `CON(e*)`: the propositional content of the speech event. -/
  content : W → List (W → Prop)

/-- In a declarative speech event `CON(e*)` is the speaker's beliefs
([hacquard-2006], her (222)). -/
def SpeechEvent.declarative (beliefs : W → List (W → Prop)) : SpeechEvent W :=
  ⟨.assertion, beliefs⟩

/-- In an imperative speech event `CON(e*)` is the addressee's To-Do
List ([hacquard-2006] after [portner-2004]). -/
def SpeechEvent.imperative (todo : W → List (W → Prop)) : SpeechEvent W :=
  ⟨.directive, todo⟩

/-! ### The induced context -/

/-- The discourse context a speech event induces at anchor world `w₀` folds `CON(e*)(w₀)` through
the update of its force, from the context in which no participant has commitments. -/
def SpeechEvent.toContext (sa : SpeechEvent W) (w₀ : W) : Role → State W :=
  (sa.content w₀).foldl sa.force.update ⊤

theorem SpeechEvent.toContext_declarative_speaker (beliefs : W → List (W → Prop)) (w₀ : W) :
    (SpeechEvent.declarative beliefs).toContext w₀ .speaker = (beliefs w₀).foldl State.assert ⊤ :=
  Force.foldl_update_apply_of_mem (c := .informational) (Finset.mem_singleton_self _) rfl _ _

theorem SpeechEvent.toContext_imperative_addressee (todo : W → List (W → Prop)) (w₀ : W) :
    (SpeechEvent.imperative todo).toContext w₀ .addressee = (todo w₀).foldl State.promote ⊤ :=
  Force.foldl_update_apply_of_mem (c := .preferential) (Finset.mem_singleton_self _) rfl _ _

theorem SpeechEvent.mem_toContext_declarative_info (beliefs : W → List (W → Prop)) (w₀ v : W) :
    v ∈ ((SpeechEvent.declarative beliefs).toContext w₀ .speaker).info ↔ ∀ p ∈ beliefs w₀, p v := by
  rw [SpeechEvent.toContext_declarative_speaker, State.foldl_assert_toExpState,
    ExpState.mem_foldl_assert_info]
  exact and_iff_right (Set.mem_univ v)

theorem SpeechEvent.toContext_imperative_le (todo : W → List (W → Prop)) (w₀ w v : W) :
    ((SpeechEvent.imperative todo).toContext w₀ .addressee).order.le w v ↔
      ∀ p ∈ todo w₀, p v → p w := by
  rw [SpeechEvent.toContext_imperative_addressee, State.foldl_promote_toExpState,
    ExpState.foldl_promote_order_le]
  exact ⟨And.right, fun h ↦ ⟨trivial, h⟩⟩

@[simp] theorem SpeechEvent.toContext_imperative_info (todo : W → List (W → Prop)) (w₀ : W) :
    ((SpeechEvent.imperative todo).toContext w₀ .addressee).info = Set.univ := by
  rw [SpeechEvent.toContext_imperative_addressee, State.foldl_promote_toExpState,
    ExpState.foldl_promote_info]
  rfl

/-! ### The licensed modal -/

/-- The necessity modal a speech event licenses is the modal of the component its force updates,
in the state of each participant the force updates ([hacquard-2006]'s epistemic and deontic
readings); a force without a component licenses none. -/
def SpeechEvent.modal (sa : SpeechEvent W) (w₀ : W) (p : W → Prop) : Prop :=
  ∃ c ∈ sa.force.target, ∀ r ∈ sa.force.holders, c.boxOn (sa.toContext w₀ r) p

@[simp] theorem SpeechEvent.modal_declarative
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p ↔
      ((SpeechEvent.declarative beliefs).toContext w₀ .speaker).boxCs p := by
  simp [SpeechEvent.modal, Force.target, Force.holders, SpeechEvent.declarative]

@[simp] theorem SpeechEvent.modal_imperative
    (todo : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.imperative todo).modal w₀ p ↔
      ((SpeechEvent.imperative todo).toContext w₀ .addressee).boxLe p := by
  simp [SpeechEvent.modal, Force.target, Force.holders, SpeechEvent.imperative]

theorem SpeechEvent.modal_declarative_iff
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p ↔
      ∀ v, (∀ q ∈ beliefs w₀, q v) → p v := by
  rw [SpeechEvent.modal_declarative]
  constructor
  · intro h v hv
    exact h v ((mem_toContext_declarative_info beliefs w₀ v).mpr hv)
  · intro h v hv
    exact h v ((mem_toContext_declarative_info beliefs w₀ v).mp hv)

/-! ### Flavor factors through the component classification -/

/-- A modal flavor targets the component its Kratzer parameter feeds, the informational one for
the modal-base flavors and the preferential one for the ordering-source flavors, as in Portner's
gloss of his (3) ([portner-2018], p. 234). -/
def _root_.Modality.ModalFlavor.target : ModalFlavor → Component
  | .epistemic      => .informational
  | .deontic        => .preferential
  | .bouletic       => .preferential
  | .circumstantial => .informational

/-- The flavor a component licenses on [hacquard-2006]'s reading of `CON(e*)`: epistemic for the
speaker's beliefs and deontic for the To-Do List. Hacquard gives an interrogative no content, so
the inquiry licenses none. -/
def Component.flavor : Component → Option ModalFlavor
  | .informational => some .epistemic
  | .preferential  => some .deontic
  | .inquisitive   => none

/-- The primary flavor a speech act licenses is the flavor of its force's component
([hacquard-2006]). -/
def _root_.Discourse.SpeechAct.Force.primaryFlavor (f : Force) : Option ModalFlavor :=
  f.target.bind Component.flavor

theorem Component.target_of_mem_flavor {c : Component} {φ : ModalFlavor} (h : φ ∈ c.flavor) :
    φ.target = c := by
  cases c <;> cases h <;> rfl

@[simp] theorem primaryFlavor_assertion :
    Force.assertion.primaryFlavor = some .epistemic := rfl

@[simp] theorem primaryFlavor_directive :
    Force.directive.primaryFlavor = some .deontic := rfl

theorem speech_act_determines_flavor :
    Force.assertion.primaryFlavor ≠ Force.directive.primaryFlavor := by decide

end Mood
