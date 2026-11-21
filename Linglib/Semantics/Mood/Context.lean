/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct.Basic
public import Linglib.Semantics.Mood.State

/-!
# Sentential force over a discourse context

A discourse context assigns each participant their discourse commitments, a mood state, so it is
a function `d : Role → Mood.State W`. A sentential force updates one component of the commitments
of some of the participants: asserting `φ` meets the speaker's context set with `φ`, and directing
`φ` promotes `φ` in the addressee's ordering.

We define `SpeechAct.Force.update`, which applies the update of the component
`SpeechAct.Force.target` of a force to the commitments of its `SpeechAct.Force.holders` and
leaves the other participants' commitments alone. It meets the context with a fixed content
(`SpeechAct.Force.isAdditive_update`), so the three consequence relations of dynamic semantics
coincide for texts of forces (`DynamicSemantics.tfae_entails`) and any two forces commute
(`SpeechAct.Force.commute_update`).

A promise promotes its content in the speaker's ordering where a directive promotes it in the
addressee's, so the two coincide exactly when both orderings already respect the content
(`SpeechAct.Force.update_promise_eq_directive_iff`). One after the other they promote the content
for every participant (`SpeechAct.Force.update_promise_update_directive`), which is the update of
Zanuttini, Pak and Portner's exhortative.

## Implementation notes

* The update of some participants' commitments is `Set.piecewise`, and that of one participant's
  is `Function.update`, in which the equations for each force are stated.
* Portner leaves interrogatives open. A question here refines the inquiry of every participant
  with the polar question whether `φ`, the question under discussion that the participants share
  in the discourse contexts of Roberts and of Portner's earlier work.
* An exclamation has no component and updates nothing.
* `SpeechAct.Force` has no exhortative, so its update is stated as a function of the context.

## References

* [portner-2018]
* [portner-2004]
* [zanuttini-pak-portner-2012]
* [zanuttini-portner-2003]
* [roberts-2012]
* [gunlogson-2001]
-/

@[expose] public section

open DynamicSemantics Function
open SpeechAct (Force)

variable {W : Type*}

namespace Mood.Component

/-- The update of a component of a mood state with `φ`: assertion for the context set, promotion
for the ordering, and the polar question whether `φ` for the inquiry. -/
def update : Component → State W → (W → Prop) → State W
  | .informational, c, φ => c.assert φ
  | .preferential, c, φ => c.promote φ
  | .inquisitive, c, φ => c.inquire (Setoid.polar {w | φ w})

@[simp] theorem update_informational (c : State W) (φ : W → Prop) :
    informational.update c φ = c.assert φ := rfl

@[simp] theorem update_preferential (c : State W) (φ : W → Prop) :
    preferential.update c φ = c.promote φ := rfl

@[simp] theorem update_inquisitive (c : State W) (φ : W → Prop) :
    inquisitive.update c φ = c.inquire (Setoid.polar {w | φ w}) := rfl

/-- The update of a component meets a state with a fixed content in that component. -/
theorem isAdditive_update (k : Component) (φ : W → Prop) : IsAdditive (k.update · φ) := by
  cases k
  exacts [State.isAdditive_assert φ, State.isAdditive_promote φ,
    State.isAdditive_inquire (Setoid.polar {w | φ w})]

end Mood.Component

namespace SpeechAct.Force

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

/-- A force with content `φ` updates the component it relates to in the commitments of each of
its holders. -/
def update (f : Force) (d : Role → State W) (φ : W → Prop) : Role → State W :=
  f.target.elim d fun k ↦ (f.holders : Set Role).piecewise (fun r ↦ k.update (d r) φ) d

variable (d : Role → State W) (φ : W → Prop)

@[simp] theorem update_assertion :
    assertion.update d φ = Function.update d .speaker ((d .speaker).assert φ) := by
  funext r; cases r <;> simp [update, target, holders]

@[simp] theorem update_directive :
    directive.update d φ = Function.update d .addressee ((d .addressee).promote φ) := by
  funext r; cases r <;> simp [update, target, holders]

@[simp] theorem update_promise :
    promise.update d φ = Function.update d .speaker ((d .speaker).promote φ) := by
  funext r; cases r <;> simp [update, target, holders]

@[simp] theorem update_question :
    question.update d φ = fun r ↦ (d r).inquire (Setoid.polar {w | φ w}) := by
  funext r; simp [update, target, holders]

@[simp] theorem update_exclamation : exclamation.update d φ = d := rfl

/-- Every force meets a discourse context with a fixed content. -/
theorem isAdditive_update (f : Force) (φ : W → Prop) : IsAdditive (f.update (W := W) · φ) := by
  cases h : f.target with
  | none => exact fun d ↦ by simp [update, h]
  | some k =>
    exact fun d ↦ by
      simpa only [update, h, Option.elim_some] using
        (k.isAdditive_update φ).piecewise (f.holders : Set Role) d

/-- Two speech acts update a discourse context to the same effect in either order. -/
theorem commute_update (f g : Force) (φ ψ : W → Prop) :
    Function.Commute (f.update (W := W) · φ) (g.update · ψ) :=
  (isAdditive_update f φ).commute (isAdditive_update g ψ)

/-- A promise and a directive with the same content coincide exactly when both participants'
orderings already respect the content, since a promise promotes it for the speaker and a directive
for the addressee ([zanuttini-pak-portner-2012], their (49)). -/
theorem update_promise_eq_directive_iff :
    promise.update d φ = directive.update d φ ↔ ∀ r, (d r).order ≤ .ofCriterion φ := by
  simp only [update_promise, update_directive, funext_iff, Role.forall_role, update_self, ne_eq,
    reduceCtorEq, not_false_eq_true, update_of_ne]
  rw [State.promote_eq_self_iff, eq_comm, State.promote_eq_self_iff]

/-- A promise after a directive with the same content promotes the content in every participant's
ordering, the update of an exhortative, which adds its content to the To-Do Lists of both the
speaker and the addressee ([zanuttini-pak-portner-2012], their (49)). -/
theorem update_promise_update_directive :
    promise.update (directive.update d φ) φ = fun r ↦ (d r).promote φ := by
  funext r; cases r <;> simp

end SpeechAct.Force
