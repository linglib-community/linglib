module

public import Linglib.Semantics.ArgumentStructure.Root.Basic

/-!
# Event structure templates

This file defines event structure templates, the terms that describe the internal structure of
the eventuality a verb names. A `Template` is built from four primitives:

* `state`, a state, written `[x ⟨STATE⟩]`;
* `act`, an action with a manner, `[x ACT⟨MANNER⟩]`;
* `become t`, a change into the state `t`, `[BECOME t]`;
* `cause c e`, a causing event `c` and what it causes, `[c CAUSE e]`.

A fifth leaf, `effector`, is the causing event of an individual causer, as in
`[x CAUSE [BECOME [y ⟨STATE⟩]]]`. Templates are sorted: `become` takes a state and gives an event,
and `cause` takes an event and a template of either sort. The achievement is
`[BECOME [x ⟨STATE⟩]]` and the accomplishment is `[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`.

We define `Template.kinds`, the kinds of entailment the primitives of a template contribute, and
the subterm relation `Template.IsSubterm`. A template with a manner and a state has a cause
(`Template.cause_mem_kinds_of_manner_of_state`), and the kinds of a subterm are among those of
the template (`Template.IsSubterm.kinds_subset`).

## Implementation notes

An individual causer is the leaf `effector`, an event with no content beyond its effector, so
that `cause` always relates two subevents.

## References

* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
* [yu-ausensi-smith-2023]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

/-- The two sorts of eventuality a template describes. -/
inductive Eventuality where
  | state
  | event
  deriving DecidableEq, Repr


/-- An event structure template, a sorted term over the primitive predicates. -/
inductive Template : Eventuality → Type where
  /-- `[x ⟨STATE⟩]`. -/
  | state : Template .state
  /-- `[x ACT⟨MANNER⟩]`, the activity. -/
  | act : Template .event
  /-- `[x]`, an eventuality with no content beyond its effector: the individual causer of
  `[x CAUSE t]`. -/
  | effector : Template .event
  /-- `[BECOME t]`. -/
  | become (t : Template .state) : Template .event
  /-- `[causing CAUSE caused]`, the caused subevent an event or a state. -/
  | cause (causing : Template .event) {σ : Eventuality} (caused : Template σ) : Template .event

namespace Template

variable {σ τ : Eventuality}

/-- The achievement `[BECOME [x ⟨STATE⟩]]`. -/
def achievement : Template .event := become state

/-- The accomplishment `[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`. -/
def accomplishment : Template .event := cause act achievement

/-- The kinds of entailment a template's primitives contribute: a state, the manner of an
action, the change of `BECOME` and the causation of `CAUSE`. -/
@[simp]
def kinds : {σ : Eventuality} → Template σ → Finset Root.Kind
  | _, state => {.state}
  | _, act => {.manner}
  | _, effector => ∅
  | _, become t => insert .result t.kinds
  | _, cause c e => insert .cause (c.kinds ∪ e.kinds)

/-- The causing subevent of a causative template. -/
def causing : Template .event → Option (Template .event)
  | cause c _ => some c
  | _ => none

/-- The caused subevent of a causative template, where it is an event. -/
def caused : Template .event → Option (Template .event)
  | cause (σ := .event) _ e => some e
  | _ => none

/-- `u` occurs in `t`. -/
inductive IsSubterm : {α β : Eventuality} → Template α → Template β → Prop
  | refl {α : Eventuality} (t : Template α) : IsSubterm t t
  | become {α : Eventuality} {u : Template α} {t : Template .state} :
      IsSubterm u t → IsSubterm u (become t)
  | causing {α β : Eventuality} {u : Template α} {c : Template .event} {e : Template β} :
      IsSubterm u c → IsSubterm u (cause c e)
  | caused {α β : Eventuality} {u : Template α} {c : Template .event} {e : Template β} :
      IsSubterm u e → IsSubterm u (cause c e)

/-- A template whose primitives include a manner and a state has `CAUSE`, since causation is
the only primitive that relates an action to a state. -/
theorem cause_mem_kinds_of_manner_of_state {t : Template σ} (hm : .manner ∈ t.kinds)
    (hs : .state ∈ t.kinds) : .cause ∈ t.kinds := by
  induction t with
  | state | act | effector => simp at hm hs
  | become _ ih =>
    simp only [kinds, Finset.mem_insert, reduceCtorEq, false_or] at hm hs ⊢
    exact ih hm hs
  | cause => simp

/-- A subterm's primitives are among the template's. -/
theorem IsSubterm.kinds_subset {u : Template τ} {t : Template σ} (h : u.IsSubterm t) :
    u.kinds ⊆ t.kinds := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | become _ ih => exact ih.trans (Finset.subset_insert _ _)
  | causing _ ih =>
    exact ih.trans (Finset.subset_union_left.trans (Finset.subset_insert _ _))
  | caused _ ih =>
    exact ih.trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))
end Template

end ArgumentStructure.EventStructure
