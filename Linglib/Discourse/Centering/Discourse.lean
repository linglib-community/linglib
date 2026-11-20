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

* `Discourse.Centering.transition`: the transition from one utterance into the next.
* `Discourse.Centering.cbs`: the backward-looking center of each utterance after the first.
* `Discourse.Centering.transitions`: the transition into each utterance after the first.

## References

* [grosz-joshi-weinstein-1995]
-/

@[expose] public section

namespace Discourse.Centering

variable {E R F : Type*} [DecidableEq E] [LinearOrder R]

/-- The transition into `cur` from `prev`, given the backward-looking center of `prev`. -/
def transition (prevCb : Option E) (prev cur : Utterance E R F) : Transition :=
  .ofCenters prevCb (cb prev cur.cf) cur.cp

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

end Discourse.Centering
