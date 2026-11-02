/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct
public import Linglib.Semantics.Mood.State

/-!
# Sentential force over a discourse context

Portner's discourse context assigns each participant discourse commitments, a mood state, so a
context is a function `Role → State W`. A sentential force updates one component of the states of
some participants: assertion meets the speaker's context set with its content, and directing
promotes the content in the addressee's ordering. Each force [meets a context with a fixed
content](##Discourse.SpeechAct.Force.isAdditive_update). Zanuttini, Pak and Portner's promissive
adds its content to the speaker's To-Do List rather than the addressee's, so a promise and a
directive with the same content [coincide exactly when both participants' orderings already
respect the content](##Discourse.SpeechAct.Force.update_promise_eq_directive_iff), so that
promoting it changes neither.

## Main definitions

* `Mood.Component.update`: the update of one component of a mood state.
* `Discourse.SpeechAct.Force.target`: the component a force updates, Portner's classification of
  the sentence moods.
* `Discourse.SpeechAct.Force.holders`: the participants whose states a force updates.
* `Discourse.SpeechAct.Force.update`: a force as an update of a discourse context.

## Implementation notes

* Portner states the updates of assertion and directing and leaves interrogatives open. A question
  here refines the inquiry of every participant, the question under discussion that the
  participants share in the discourse contexts of Roberts and of Portner's earlier work.
* An exclamation has no component and updates nothing.

## References

* [portner-2018]
* [portner-2004]
* [zanuttini-pak-portner-2012]
* [zanuttini-portner-2003]
* [roberts-2012]
* [gunlogson-2001]
-/

@[expose] public section

open DynamicSemantics
open Discourse.SpeechAct (Force)

variable {W : Type*}

namespace Mood

/-- The update of a component of a mood state with `φ`: assertion for the context set, promotion
for the ordering, and the polar question whether `φ` for the inquiry. -/
def Component.update : Component → State W → (W → Prop) → State W
  | .informational, c, φ => c.assert φ
  | .preferential, c, φ => c.promote φ
  | .inquisitive, c, φ => c.inquire (Setoid.polar {w | φ w})

@[simp] theorem Component.update_informational (c : State W) (φ : W → Prop) :
    Component.informational.update c φ = c.assert φ := rfl

@[simp] theorem Component.update_preferential (c : State W) (φ : W → Prop) :
    Component.preferential.update c φ = c.promote φ := rfl

@[simp] theorem Component.update_inquisitive (c : State W) (φ : W → Prop) :
    Component.inquisitive.update c φ = c.inquire (Setoid.polar {w | φ w}) := rfl

/-- The update of every component meets a state with a fixed content in that component. -/
theorem Component.isAdditive_update (k : Component) (φ : W → Prop) :
    IsAdditive (k.update · φ) := by
  cases k
  exacts [State.isAdditive_assert φ, State.isAdditive_promote φ,
    State.isAdditive_inquire (Setoid.polar {w | φ w})]

end Mood

namespace Discourse.SpeechAct.Force

open Mood

/-- The component of the mood state a force relates to, Portner's classification of the
sentence moods: an assertion relates to the context set and a directive to the ordering. A
promise is jussive like a directive, its content added to a To-Do List, and a question relates
to the inquiry. An exclamation relates to none: its widening acts on the domain of its
wh-operator ([zanuttini-portner-2003]). -/
def target : Force → Option Component
  | .assertion => some .informational
  | .directive | .promise => some .preferential
  | .question => some .inquisitive
  | .exclamation => none

theorem target_eq_none_iff {f : Force} : f.target = none ↔ f = .exclamation := by
  cases f <;> simp [target]

/-- The participants whose discourse commitments a force updates: the speaker's for an assertion
and the addressee's for a directive, as in Portner's definitions of assertion and directing; the
speaker's for a promise, whose content is a property of the speaker
([zanuttini-pak-portner-2012], their (49)); every participant's for a question; and none for an
exclamation. -/
def holders : Force → Finset Role
  | assertion | promise => {.speaker}
  | directive => {.addressee}
  | question => .univ
  | exclamation => ∅

/-- A force with content `φ` updates the component it relates to in the state of each of its
holders and leaves the other participants' states alone. -/
def update (f : Force) (d : Role → State W) (φ : W → Prop) : Role → State W :=
  fun r ↦ if r ∈ f.holders then f.target.elim (d r) fun c ↦ c.update (d r) φ else d r

variable (d : Role → State W) (φ : W → Prop)

theorem update_apply_of_mem {f : Force} {r : Role} {c : Component} (hr : r ∈ f.holders)
    (hc : f.target = some c) : f.update d φ r = c.update (d r) φ := by
  simp only [update, hr, ↓reduceIte, hc, Option.elim_some]

theorem update_apply_of_notMem {f : Force} {r : Role} (hr : r ∉ f.holders) :
    f.update d φ r = d r := by
  simp only [update, hr, ↓reduceIte]

/-- Every force meets a discourse context with a fixed content, so that for texts of forces the
three consequence relations of dynamic semantics coincide (`DynamicSemantics.tfae_entails`). -/
theorem isAdditive_update (f : Force) (φ : W → Prop) : IsAdditive (f.update · φ) := fun d ↦
  funext fun r ↦ show f.update d φ r = d r ⊓ f.update ⊤ φ r by
    by_cases hr : r ∈ f.holders
    · cases hc : f.target with
      | none => simp [update, hr, hc]
      | some k =>
        rw [update_apply_of_mem _ _ hr hc, update_apply_of_mem _ _ hr hc]
        exact k.isAdditive_update φ (d r)
    · rw [update_apply_of_notMem _ _ hr, update_apply_of_notMem _ _ hr]
      exact (inf_top_eq _).symm

@[simp] theorem update_assertion_speaker : assertion.update d φ .speaker = (d .speaker).assert φ :=
  update_apply_of_mem (c := .informational) d φ (Finset.mem_singleton_self _) rfl

@[simp] theorem update_assertion_addressee : assertion.update d φ .addressee = d .addressee :=
  update_apply_of_notMem d φ (by decide)

@[simp] theorem update_directive_speaker : directive.update d φ .speaker = d .speaker :=
  update_apply_of_notMem d φ (by decide)

@[simp] theorem update_directive_addressee :
    directive.update d φ .addressee = (d .addressee).promote φ :=
  update_apply_of_mem (c := .preferential) d φ (Finset.mem_singleton_self _) rfl

@[simp] theorem update_promise_speaker : promise.update d φ .speaker = (d .speaker).promote φ :=
  update_apply_of_mem (c := .preferential) d φ (Finset.mem_singleton_self _) rfl

@[simp] theorem update_promise_addressee : promise.update d φ .addressee = d .addressee :=
  update_apply_of_notMem d φ (by decide)

@[simp] theorem update_question (r : Role) :
    question.update d φ r = (d r).inquire (Setoid.polar {w | φ w}) :=
  update_apply_of_mem (c := .inquisitive) d φ (Finset.mem_univ r) rfl

@[simp] theorem update_exclamation : exclamation.update d φ = d :=
  funext fun _ ↦ update_apply_of_notMem d φ (Finset.notMem_empty _)

/-- A promise and a directive with the same content coincide exactly when both participants'
orderings already respect the content, since a promise promotes it for the speaker and a directive
for the addressee ([zanuttini-pak-portner-2012], their (49)). -/
theorem update_promise_eq_directive_iff :
    promise.update d φ = directive.update d φ ↔ ∀ r, (d r).order ≤ .ofCriterion φ := by
  simp only [funext_iff, Role.forall_role, update_promise_speaker, update_directive_speaker,
    update_promise_addressee, update_directive_addressee]
  rw [State.promote_eq_self_iff, eq_comm, State.promote_eq_self_iff]

/-- Folding contents through a force folds them through the update of its component in the state
of each holder. -/
theorem foldl_update_apply_of_mem {f : Force} {r : Role} {c : Component} (hr : r ∈ f.holders)
    (hc : f.target = some c) (l : List (W → Prop)) (d : Role → State W) :
    l.foldl f.update d r = l.foldl c.update (d r) := by
  induction l generalizing d with
  | nil => rfl
  | cons φ l ih => rw [List.foldl_cons, ih, update_apply_of_mem d φ hr hc, List.foldl_cons]

end Discourse.SpeechAct.Force
