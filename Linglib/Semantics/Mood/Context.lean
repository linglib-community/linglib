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
a function `d : ι → Mood.State W`. A sentential force updates one component of the commitments
of some of the participants: asserting `φ` meets the speaker's context set with `φ`, and directing
`φ` promotes `φ` in the addressee's ordering.

We define `Mood.Component.updateOn k s d φ`, the context that updates the component `k` with `φ`
in the commitments of the participants in `s` and agrees with `d` elsewhere, and
`SpeechAct.Force.update`, which updates the component `SpeechAct.Force.target` of a force for the
participants `SpeechAct.Force.holders`. Such an update meets the context with a fixed content
(`Mood.Component.isAdditive_updateOn`), so the three consequence relations of dynamic semantics
coincide for texts of forces (`DynamicSemantics.tfae_entails`) and any two forces commute
(`SpeechAct.Force.commute_update`). Updating the participants in `s` and updating those in `t`
give the same context exactly when the commitments of each participant in only one of the two
sets already accept the content (`Mood.Component.updateOn_eq_updateOn_iff`).

A promise promotes its content in the speaker's ordering where a directive promotes it in the
addressee's, so the two coincide exactly when both orderings already respect the content
(`SpeechAct.Force.update_promise_eq_directive_iff`). One after the other they promote the content
for every participant (`SpeechAct.Force.update_promise_update_directive`), which is the update of
Zanuttini, Pak and Portner's exhortative.

## Implementation notes

* The set of participants is an argument of `Mood.Component.updateOn` rather than fixed by the
  component, since the sources differ on it: Portner's assertion updates the speaker's context
  set and mentions the alternative of updating every participant's, and the three jussive clause
  types of Zanuttini, Pak and Portner add to the To-Do List of the speaker, of the addressee, or
  of both.
* `Mood.Component.updateOn` decides membership in `s` classically, as `Set.indicator` does, so
  that no `Decidable` instance appears in statements about it.
* Portner leaves interrogatives open. A question here refines the inquiry of every participant
  with the polar question whether `φ`, the question under discussion that the participants share
  in the discourse contexts of Roberts and of Portner's earlier work.
* An exclamation has no component and updates nothing.
* `SpeechAct.Force` has no exhortative, so its update is stated on `Mood.Component.updateOn`.

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
open scoped symmDiff

variable {ι W : Type*}

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

/-! ### Updating the commitments of some participants -/

open Classical in
/-- The update of the component `k` with `φ` in the discourse commitments of the participants in
`s`, which leaves the commitments of the other participants alone. -/
noncomputable def updateOn (k : Component) (s : Set ι) (d : ι → State W) (φ : W → Prop) :
    ι → State W :=
  s.piecewise (fun i ↦ k.update (d i) φ) d

variable {k : Component} {s t : Set ι} {d : ι → State W} {φ : W → Prop} {i : ι}

open Classical in
@[simp] theorem updateOn_apply_of_mem (hi : i ∈ s) : k.updateOn s d φ i = k.update (d i) φ :=
  Set.piecewise_eq_of_mem _ _ _ hi

open Classical in
@[simp] theorem updateOn_apply_of_notMem (hi : i ∉ s) : k.updateOn s d φ i = d i :=
  Set.piecewise_eq_of_notMem _ _ _ hi

@[simp] theorem updateOn_empty : k.updateOn ∅ d φ = d :=
  funext fun i ↦ updateOn_apply_of_notMem (Set.notMem_empty i)

@[simp] theorem updateOn_univ : k.updateOn Set.univ d φ = fun i ↦ k.update (d i) φ :=
  funext fun i ↦ updateOn_apply_of_mem (Set.mem_univ i)

open Classical in
/-- The update of a component for some participants meets the context with a fixed content. -/
theorem isAdditive_updateOn (k : Component) (s : Set ι) (φ : W → Prop) :
    IsAdditive (k.updateOn (W := W) s · φ) :=
  (k.isAdditive_update φ).piecewise s

/-- Updating the participants in `s ∪ t` is updating those in `t` and then those in `s`. -/
theorem updateOn_union : k.updateOn (s ∪ t) d φ = k.updateOn s (k.updateOn t d φ) φ := by
  have h (c : State W) : k.update (k.update c φ) φ = k.update c φ :=
    (k.isAdditive_update φ).isFixedPt_apply c
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht, h]

/-- Updating the participants in `s` and updating those in `t` give the same context exactly
when the commitments of each participant in only one of the two sets accept the content. -/
theorem updateOn_eq_updateOn_iff :
    k.updateOn s d φ = k.updateOn t d φ ↔ ∀ i ∈ s ∆ t, IsFixedPt (k.update · φ) (d i) := by
  refine funext_iff.trans (forall_congr' fun i ↦ ?_)
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t
  · simp [Set.mem_symmDiff, hs, ht]
  · simp [Set.mem_symmDiff, hs, ht, IsFixedPt]
  · simpa [Set.mem_symmDiff, hs, ht, IsFixedPt] using
      eq_comm (a := d i) (b := k.update (d i) φ)
  · simp [Set.mem_symmDiff, hs, ht]

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
def holders : Force → Set Role
  | assertion | promise => {.speaker}
  | directive => {.addressee}
  | question => Set.univ
  | exclamation => ∅

/-- A force with content `φ` updates the component it relates to in the commitments of each of
its holders. -/
noncomputable def update (f : Force) (d : Role → State W) (φ : W → Prop) : Role → State W :=
  f.target.elim d (·.updateOn f.holders d φ)

variable (d : Role → State W) (φ : W → Prop)

@[simp] theorem update_assertion :
    assertion.update d φ = Component.informational.updateOn {.speaker} d φ := rfl

@[simp] theorem update_directive :
    directive.update d φ = Component.preferential.updateOn {.addressee} d φ := rfl

@[simp] theorem update_promise :
    promise.update d φ = Component.preferential.updateOn {.speaker} d φ := rfl

@[simp] theorem update_question :
    question.update d φ = fun r ↦ (d r).inquire (Setoid.polar {w | φ w}) :=
  Component.updateOn_univ

@[simp] theorem update_exclamation : exclamation.update d φ = d := rfl

/-- Every force meets a discourse context with a fixed content. -/
theorem isAdditive_update (f : Force) (φ : W → Prop) : IsAdditive (f.update (W := W) · φ) := by
  cases f
  exacts [Component.isAdditive_updateOn _ _ φ, Component.isAdditive_updateOn _ _ φ,
    Component.isAdditive_updateOn _ _ φ, Component.isAdditive_updateOn _ _ φ, isAdditive_id]

/-- Two speech acts update a discourse context to the same effect in either order. -/
theorem commute_update (f g : Force) (φ ψ : W → Prop) :
    Function.Commute (f.update (W := W) · φ) (g.update · ψ) :=
  (isAdditive_update f φ).commute (isAdditive_update g ψ)

/-- A promise and a directive with the same content coincide exactly when both participants'
orderings already respect the content, since a promise promotes it for the speaker and a directive
for the addressee ([zanuttini-pak-portner-2012], their (49)). -/
theorem update_promise_eq_directive_iff :
    promise.update d φ = directive.update d φ ↔ ∀ r, (d r).order ≤ .ofCriterion φ := by
  simp [Component.updateOn_eq_updateOn_iff, Set.mem_symmDiff, IsFixedPt,
    State.promote_eq_self_iff]

/-- A promise after a directive with the same content promotes the content in every participant's
ordering, the update of an exhortative, which adds its content to the To-Do Lists of both the
speaker and the addressee ([zanuttini-pak-portner-2012], their (49)). -/
theorem update_promise_update_directive :
    promise.update (directive.update d φ) φ = Component.preferential.updateOn Set.univ d φ := by
  rw [update_promise, update_directive, ← Component.updateOn_union]
  exact congrArg (Component.preferential.updateOn · d φ) (Set.ext fun r ↦ by cases r <;> simp)

end SpeechAct.Force
