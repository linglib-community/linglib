module

public import Linglib.Discourse.Centering.Center
public import Linglib.Discourse.Centering.Transition
public import Mathlib.Data.List.Zip

/-!
# Centering theory: the centers and transitions of a discourse

This file reads the backward-looking centers and the transitions off a discourse, a list of
utterances: each utterance after the first has the backward-looking center of its
forward-looking centers after the utterance before it, and the transition into it compares that
center with the one before and with its own preferred center.

## Main definitions

* `Centering.transition`: the transition from one utterance into the next.
* `Centering.extendedTransition`: the transition of Brennan, Friedman, and Pollard's
  table from one utterance into the next.
* `Centering.cbs`: the backward-looking center of each utterance after the first.
* `Centering.transitions`: the transition into each utterance after the first.

## Main results

* `Centering.transition_eq_toTransition`: the transition is the one that the extended
  transition refines.

## Implementation notes

An utterance with no backward-looking center has no extended transition, and
`extendedTransition` is `⊥` there.

## References

* [grosz-joshi-weinstein-1995]
* [brennan-friedman-pollard-1987]
-/

@[expose] public section

namespace Centering

variable {E R F : Type*} [DecidableEq E] [LinearOrder R]

/-- The transition into `cur` from `prev`, given the backward-looking center of `prev`. -/
def transition (prevCb : Option E) (prev cur : Utterance E R F) : Transition :=
  .ofCenters prevCb (cb prev cur.cf) cur.cp

/-- The transition of [brennan-friedman-pollard-1987] into `cur` from `prev`, given the
backward-looking center of `prev`: `⊥` when `cur` has no backward-looking center. -/
def extendedTransition (prevCb : Option E) (prev cur : Utterance E R F) :
    WithBot ExtendedTransition :=
  match cb prev cur.cf with
  | some c => ExtendedTransition.ofCenters prevCb c cur.cp
  | none => ⊥

section extendedTransition

variable {prevCb : Option E} {prev cur : Utterance E R F} {c : E}

theorem extendedTransition_of_cb_eq_none (prevCb : Option E) (h : cb prev cur.cf = none) :
    extendedTransition prevCb prev cur = ⊥ := by
  simp [extendedTransition, h]

theorem extendedTransition_of_cb_eq_some (prevCb : Option E) (h : cb prev cur.cf = some c) :
    extendedTransition prevCb prev cur = ExtendedTransition.ofCenters prevCb c cur.cp := by
  simp [extendedTransition, h]

@[simp] theorem extendedTransition_eq_bot_iff :
    extendedTransition prevCb prev cur = ⊥ ↔ cb prev cur.cf = none := by
  rcases h : cb prev cur.cf with - | c
  · simp [extendedTransition_of_cb_eq_none _ h]
  · simp [extendedTransition_of_cb_eq_some _ h]

/-- The transition into an utterance is the one that its extended transition refines. -/
theorem transition_eq_toTransition {t : ExtendedTransition}
    (h : extendedTransition prevCb prev cur = t) :
    transition prevCb prev cur = t.toTransition := by
  rcases hc : cb prev cur.cf with - | c
  · rw [extendedTransition_of_cb_eq_none _ hc] at h
    exact absurd h WithBot.bot_ne_coe
  · rw [extendedTransition_of_cb_eq_some _ hc, WithBot.coe_inj] at h
    rw [transition, hc, ← h]
    rfl

end extendedTransition

/-- The backward-looking center of each utterance of `d` after the first. -/
def cbs (d : List (Utterance E R F)) : List (Option E) :=
  List.zipWith (fun prev cur ↦ cb prev cur.cf) d d.tail

/-- The transition into each utterance of `d` after the first, the first of them with no prior
center. -/
def transitions (d : List (Utterance E R F)) : List Transition :=
  List.zipWith3 transition (none :: cbs d) d d.tail

@[simp] theorem cbs_nil : cbs ([] : List (Utterance E R F)) = [] := rfl

@[simp] theorem cbs_singleton (u : Utterance E R F) : cbs [u] = [] := rfl

@[simp] theorem cbs_cons_cons (u₁ u₂ : Utterance E R F) (d : List (Utterance E R F)) :
    cbs (u₁ :: u₂ :: d) = cb u₁ u₂.cf :: cbs (u₂ :: d) := rfl

@[simp] theorem length_cbs (d : List (Utterance E R F)) : (cbs d).length = d.length - 1 := by
  simp [cbs, List.length_zipWith]

@[simp] theorem transitions_nil : transitions ([] : List (Utterance E R F)) = [] := rfl

@[simp] theorem transitions_singleton (u : Utterance E R F) : transitions [u] = [] := rfl

@[simp] theorem length_transitions (d : List (Utterance E R F)) :
    (transitions d).length = d.length - 1 := by
  rw [transitions, ← List.zipWith_zipWith_left (fun (f : Utterance E R F → Transition) ↦ f)
    transition]
  simp [List.length_zipWith]

end Centering
