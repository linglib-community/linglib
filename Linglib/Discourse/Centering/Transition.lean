module

public import Linglib.Discourse.Centering.Basic
public import Mathlib.Data.List.Defs

/-!
# Centering theory: transitions

Grosz, Joshi, and Weinstein classify the move from one utterance to the next by whether the
backward-looking center is kept and, if so, whether it is the preferred center: continuation,
retaining, or shifting. Rule 2 orders the three, continuation first, and prefers sequences of
earlier transitions to sequences of later ones. This file classifies a pair of utterances from
its centers, scans a discourse for the centers and transitions of each utterance after the
first, and carries Rule 2's order as the `LinearOrder` on `Transition`.

## Main declarations

* `Discourse.Centering.Transition`: the three transition types, linearly ordered by Rule 2.
* `Transition.ofCenters`: the transition determined by the prior center, the current center, and
  the current preferred center.
* `Discourse.Centering.transition`: the transition into an utterance from the previous one,
  given the prior center.
* `Discourse.Centering.cbs` and `transitions`: the centers and transitions along a discourse.

## Implementation notes

The paper's definitions presuppose a prior backward-looking center. When there is none, as for
the second utterance of a segment, the center counts as kept, so the utterance continues or
retains according to whether its center is its preferred center: the proposal of Walker, Iida,
and Cote that [poesio-stevenson-eugenio-hitzeman-2004] reports, on which the first utterance's
center is underspecified until the second is processed. An utterance with no backward-looking
center shifts, as the paper's shifting clause reads when the center is undefined.

Rule 2 prefers sequences of continuations to sequences of retentions and those to sequences of
shifts, and in particular prefers a pair of continuations to a pair of retentions. The order on
`Transition` is its content on single transitions; a study compares sequences by that order
pointwise.

## References

* [grosz-joshi-weinstein-1995]
* [poesio-stevenson-eugenio-hitzeman-2004]
-/

@[expose] public section

namespace Discourse.Centering

/-- The transition into an utterance: its backward-looking center is kept and is its preferred
center, kept but not preferred, or changed. -/
inductive Transition where
  | continuation
  | retaining
  | shifting
  deriving DecidableEq, Repr

namespace Transition

/-- Rule 2's rank: continuation over retaining over shifting. -/
@[simp] def rank : Transition → ℕ
  | .continuation => 2
  | .retaining => 1
  | .shifting => 0

/-- Rule 2's order on single transitions, continuation the greatest. -/
instance : LinearOrder Transition :=
  LinearOrder.lift' rank fun a b h ↦ by cases a <;> cases b <;> simp_all

theorem retaining_lt_continuation : retaining < continuation := by decide

theorem shifting_lt_retaining : shifting < retaining := by decide

variable {E : Type*} [DecidableEq E]

/-- The transition determined by the prior backward-looking center, the current one, and the
current preferred center. The center is kept when it is defined and, if the prior center is
defined, equal to it. -/
def ofCenters : Option E → Option E → Option E → Transition
  | _, none, _ => .shifting
  | prevCb, some c, curCp =>
    if ∀ p ∈ prevCb, p = c then if curCp = some c then .continuation else .retaining
    else .shifting

@[simp] theorem ofCenters_none (prevCb curCp : Option E) :
    ofCenters prevCb none curCp = .shifting := rfl

theorem ofCenters_some (prevCb curCp : Option E) (c : E) : ofCenters prevCb (some c) curCp =
    if ∀ p ∈ prevCb, p = c then if curCp = some c then .continuation else .retaining
    else .shifting := rfl

theorem ofCenters_some_some (p c : E) (curCp : Option E) : ofCenters (some p) (some c) curCp =
    if p = c then if curCp = some c then .continuation else .retaining else .shifting := by
  simp [ofCenters_some]

end Transition

variable {E R : Type*} [DecidableEq E] [LinearOrder R]

/-- The transition into `cur` from `prev`, given the backward-looking center of `prev`. -/
def transition (prevCb : Option E) (prev cur : Utterance E R) : Transition :=
  .ofCenters prevCb (cb prev cur) cur.cp

/-! ### Scanning a discourse -/

/-- The backward-looking center of each utterance of `d` after the first. -/
def cbs (d : List (Utterance E R)) : List (Option E) := List.zipWith cb d d.tail

/-- The transition into each utterance of `d` after the first, the first of them with no prior
center. -/
def transitions (d : List (Utterance E R)) : List Transition :=
  List.zipWith3 Transition.ofCenters (none :: cbs d) (cbs d) (d.tail.map Utterance.cp)

@[simp] theorem cbs_nil : cbs ([] : List (Utterance E R)) = [] := rfl

@[simp] theorem cbs_singleton (u : Utterance E R) : cbs [u] = [] := rfl

@[simp] theorem cbs_cons_cons (u₁ u₂ : Utterance E R) (d : List (Utterance E R)) :
    cbs (u₁ :: u₂ :: d) = cb u₁ u₂ :: cbs (u₂ :: d) := rfl

@[simp] theorem length_cbs (d : List (Utterance E R)) : (cbs d).length = d.length - 1 := by
  simp [cbs, List.length_zipWith]

@[simp] theorem transitions_nil : transitions ([] : List (Utterance E R)) = [] := rfl

@[simp] theorem transitions_singleton (u : Utterance E R) : transitions [u] = [] := rfl

theorem transitions_cons_cons (u₁ u₂ : Utterance E R) (d : List (Utterance E R)) :
    transitions (u₁ :: u₂ :: d) = transition none u₁ u₂ ::
      List.zipWith3 Transition.ofCenters (cbs (u₁ :: u₂ :: d)) (cbs (u₂ :: d))
        (d.map Utterance.cp) := rfl

private theorem length_zipWith3 : ∀ {p c q : List (Option E)}, p.length = c.length + 1 →
    q.length = c.length → (List.zipWith3 Transition.ofCenters p c q).length = c.length
  | [], _, _, hp, _ => (Nat.succ_ne_zero _ hp.symm).elim
  | _ :: _, [], q, _, _ => by cases q <;> rfl
  | _ :: _, _ :: _, [], _, hq => (Nat.succ_ne_zero _ hq.symm).elim
  | _ :: _, _ :: _, _ :: _, hp, hq =>
    congrArg Nat.succ (length_zipWith3 (Nat.succ_injective hp) (Nat.succ_injective hq))

@[simp] theorem length_transitions (d : List (Utterance E R)) :
    (transitions d).length = d.length - 1 := by
  unfold transitions
  exact (length_zipWith3 (by simp) (by simp)).trans (length_cbs d)

end Discourse.Centering
