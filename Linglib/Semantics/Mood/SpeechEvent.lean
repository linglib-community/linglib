/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct
public import Linglib.Semantics.Mood.State
public import Linglib.Semantics.Modality.Basic

/-!
# The speech event and its content

Hacquard (pp. 141–3) adopts the Speech Act Phrase of Speas and Tenny, whose head introduces a
speech event `e*` and encodes illocutionary force, and adds that the speech event has content
`CON(e*)`: the speaker's beliefs for a declarative, the addressee's To-Do List for an
imperative. A modal bound by `e*` reads `CON(e*)` as its conversational background, so the
speech act fixes the modal's flavor without lexical ambiguity. Here `CON(e*)` enters the mood
state through the update of the force's component, and the licensed modal and flavor are read
off that component.

## Main definitions

* `Discourse.SpeechAct.Force.target`: Portner's classification of a force by the component of
  the mood state it relates to.
* `Mood.SpeechEvent`: a force together with `CON(e*)`.
* `Mood.SpeechEvent.toState`, `Mood.SpeechEvent.modal`: the induced state and its modal.
* `Discourse.SpeechAct.Force.primaryFlavor`: Hacquard's flavor of a speech act, read off its
  component.

## Implementation notes

* Speas and Tenny derive four speech acts, declarative, interrogative, imperative and
  subjunctive; `Discourse.SpeechAct.Force` has no counterpart of the subjunctive and adds the
  promise and the exclamation.
* Hacquard gives content only to declaratives and imperatives, so an interrogative induces the
  initial state and its component licenses no flavor.
* Which event binds a modal is the business of `Semantics/Modality/EventRelativity.lean`.

## References

* [hacquard-2006]
* [speas-tenny-2003]
* [portner-2004]
* [portner-2018]
* [zanuttini-pak-portner-2012]
* [zanuttini-portner-2003]
* [kratzer-1981]
-/

@[expose] public section

namespace Mood

open DynamicSemantics
open Modality (ModalFlavor)
open Discourse.SpeechAct (Force)

variable {W : Type*}

/-! ### The component of a force -/

/-- The component of the mood state a force relates to, Portner's classification of the
sentence moods: an assertion relates to the context set and a directive to the ordering. A
promise is jussive like a directive, its content added to the speaker's To-Do List rather than
the addressee's ([zanuttini-pak-portner-2012], their (49)), and a question relates to the
inquiry. An exclamation relates to none: its widening acts on the domain of its wh-operator
([zanuttini-portner-2003]). -/
def _root_.Discourse.SpeechAct.Force.target : Force → Option Component
  | .assertion => some .informational
  | .directive | .promise => some .preferential
  | .question => some .inquisitive
  | .exclamation => none

theorem _root_.Discourse.SpeechAct.Force.target_eq_none_iff {f : Force} :
    f.target = none ↔ f = .exclamation := by
  cases f <;> simp [Force.target]

/-! ### Speech events -/

/-- A speech act event `e*` with its content `CON(e*)`
([hacquard-2006], her assumption 4, pp. 142–3). -/
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

/-! ### The induced state -/

/-- The state a speech event induces at anchor world `w₀` folds `CON(e*)(w₀)` through the update
of the force's component, and is the initial state for a force without content. -/
def SpeechEvent.toState (sa : SpeechEvent W) (w₀ : W) : ExpState W :=
  match sa.force.target with
  | some .informational => (sa.content w₀).foldl ExpState.assert ExpState.init
  | some .preferential => (sa.content w₀).foldl ExpState.promote ExpState.init
  | some .inquisitive | none => ExpState.init

@[simp] theorem SpeechEvent.toState_declarative
    (beliefs : W → List (W → Prop)) (w₀ : W) :
    (SpeechEvent.declarative beliefs).toState w₀ =
      (beliefs w₀).foldl ExpState.assert ExpState.init := rfl

@[simp] theorem SpeechEvent.toState_imperative
    (todo : W → List (W → Prop)) (w₀ : W) :
    (SpeechEvent.imperative todo).toState w₀ =
      (todo w₀).foldl ExpState.promote ExpState.init := rfl

theorem SpeechEvent.mem_toState_declarative_info
    (beliefs : W → List (W → Prop)) (w₀ v : W) :
    v ∈ ((SpeechEvent.declarative beliefs).toState w₀).info ↔
      ∀ p ∈ beliefs w₀, p v := by
  rw [SpeechEvent.toState_declarative, ExpState.mem_foldl_assert_info]
  simp [ExpState.init]

theorem SpeechEvent.toState_imperative_le
    (todo : W → List (W → Prop)) (w₀ w v : W) :
    ((SpeechEvent.imperative todo).toState w₀).order.le w v ↔
      ∀ p ∈ todo w₀, p v → p w := by
  rw [SpeechEvent.toState_imperative, ExpState.foldl_promote_order_le]
  exact ⟨And.right, fun h ↦ ⟨trivial, h⟩⟩

theorem SpeechEvent.toState_imperative_info
    (todo : W → List (W → Prop)) (w₀ : W) :
    ((SpeechEvent.imperative todo).toState w₀).info = Set.univ := by
  rw [SpeechEvent.toState_imperative, ExpState.foldl_promote_info]
  rfl

/-! ### The licensed modal -/

/-- The necessity modal a speech event licenses is the modal of its force's component on the
induced state ([hacquard-2006]'s epistemic and deontic readings); a force without a component
licenses none. -/
def SpeechEvent.modal (sa : SpeechEvent W) (w₀ : W) (p : W → Prop) : Prop :=
  ∃ c ∈ sa.force.target, c.boxOn (State.ofExpState (sa.toState w₀)) p

@[simp] theorem SpeechEvent.modal_declarative
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p ↔
      ((SpeechEvent.declarative beliefs).toState w₀).boxCs p := by
  simp [SpeechEvent.modal, SpeechEvent.declarative, Force.target]

@[simp] theorem SpeechEvent.modal_imperative
    (todo : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.imperative todo).modal w₀ p ↔
      ((SpeechEvent.imperative todo).toState w₀).boxLe p := by
  simp [SpeechEvent.modal, SpeechEvent.imperative, Force.target]

theorem SpeechEvent.modal_declarative_iff
    (beliefs : W → List (W → Prop)) (w₀ : W) (p : W → Prop) :
    (SpeechEvent.declarative beliefs).modal w₀ p ↔
      ∀ v, (∀ q ∈ beliefs w₀, q v) → p v := by
  rw [SpeechEvent.modal_declarative]
  constructor
  · intro h v hv
    exact h v ((mem_toState_declarative_info beliefs w₀ v).mpr hv)
  · intro h v hv
    exact h v ((mem_toState_declarative_info beliefs w₀ v).mp hv)

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

/-! ### Worked example: "You can leave"

Same modal, same proposition, different speech events: the force,
routed through its targeted component, determines the modal
domain. -/

/-- The two outcomes are leaving and staying. -/
inductive LeaveWorld where | leave | stay
  deriving DecidableEq, Repr, Inhabited

/-- In the declarative context the speaker's evidence is compatible with both outcomes. -/
def declarativeEvidence : SpeechEvent LeaveWorld :=
  .declarative (fun _ ↦ [])

/-- In the imperative context *leave* is on the addressee's To-Do List. -/
def imperativePermission : SpeechEvent LeaveWorld :=
  .imperative (fun _ ↦ [(· = .leave)])

theorem declarative_leave_not_necessary :
    ¬ declarativeEvidence.modal .leave (· = .leave) := by
  intro h
  exact LeaveWorld.noConfusion ((SpeechEvent.modal_declarative _ _ _).mp h .stay
    ((SpeechEvent.mem_toState_declarative_info _ _ _).mpr (by simp)))

theorem imperative_leave_required :
    imperativePermission.modal .leave (· = .leave) := by
  have hchar : ∀ v ∈ (imperativePermission.toState LeaveWorld.leave).optimal,
      v = LeaveWorld.leave := by
    intro v hv
    by_contra hstay
    have hle : (imperativePermission.toState LeaveWorld.leave).order.le
        LeaveWorld.leave v :=
      (SpeechEvent.toState_imperative_le _ LeaveWorld.leave LeaveWorld.leave v).mpr
        (fun p hp _ ↦ by rw [List.mem_singleton] at hp; subst hp; rfl)
    have hmem : LeaveWorld.leave ∈ (imperativePermission.toState LeaveWorld.leave).info :=
      (SpeechEvent.toState_imperative_info _ LeaveWorld.leave) ▸ Set.mem_univ _
    have hvl := hv.2 hmem hle
    exact hstay ((SpeechEvent.toState_imperative_le _ LeaveWorld.leave v
      LeaveWorld.leave).mp hvl (· = LeaveWorld.leave) (List.mem_singleton_self _) rfl)
  exact (SpeechEvent.modal_imperative _ _ _).mpr hchar

end Mood
