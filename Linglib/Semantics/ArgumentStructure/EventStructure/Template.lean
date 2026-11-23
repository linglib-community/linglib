module

public import Linglib.Semantics.ArgumentStructure.Root.Basic

/-!
# Event structure templates

This file defines event structure templates, the terms that describe the internal structure of
the eventuality a verb names. A template is built from a state `[x ⟨STATE⟩]`, an action
`[x ACT⟨MANNER⟩]`, a change `[BECOME t]` and causation `[c CAUSE e]`. Templates are sorted:
`BECOME` takes a state and gives an event, and `CAUSE` takes an event and a template of either
sort.

## Main definitions

* `EventStructure.Template`: the templates of a sort, with constructors `state`, `act`,
  `effector`, `become` and `cause`.
* `Template.achievement`: the template `[BECOME [x ⟨STATE⟩]]`.
* `Template.accomplishment`: the template `[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`.
* `Template.kinds`: the kinds of entailment the primitives of a template contribute.
* `Template.IsSubterm`: the subterm relation.

## Main results

* `Template.cause_mem_kinds_of_manner_of_state`: a template with a manner and a state has a
  cause.
* `Template.IsSubterm.kinds_subset`: the kinds of a subterm are among those of the template.

## Implementation notes

An individual causer is the leaf `effector`, an event with no content beyond its effector, as in
`[x CAUSE [BECOME [y ⟨STATE⟩]]]`, so that `cause` always relates two subevents.

## References

* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
* [yu-ausensi-smith-2023]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

/-- The sort of an eventuality, a state or an event. -/
inductive Eventuality where
  | state
  | event
  deriving DecidableEq, Repr


/-- An event structure template of a given sort. -/
inductive Template : Eventuality → Type where
  /-- `[x ⟨STATE⟩]`. -/
  | state : Template .state
  /-- `[x ACT⟨MANNER⟩]`, an action. -/
  | act : Template .event
  /-- `[x]`, the event of an individual causer, with no content beyond its effector. -/
  | effector : Template .event
  /-- `[BECOME t]`. -/
  | become (t : Template .state) : Template .event
  /-- `[causing CAUSE caused]`, where `caused` is an event or a state. -/
  | cause (causing : Template .event) {σ : Eventuality} (caused : Template σ) : Template .event

namespace Template

variable {σ τ : Eventuality}

/-- The achievement `[BECOME [x ⟨STATE⟩]]`. -/
def achievement : Template .event := become state

/-- The accomplishment `[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`. -/
def accomplishment : Template .event := cause act achievement

/-- The kinds of entailment the primitives of a template contribute. -/
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

/-- The caused subevent of a causative template, when it is an event. -/
def caused : Template .event → Option (Template .event)
  | cause (σ := .event) _ e => some e
  | _ => none

/-- `u.IsSubterm t` means that `u` occurs in `t`. -/
inductive IsSubterm : {α β : Eventuality} → Template α → Template β → Prop
  | refl {α : Eventuality} (t : Template α) : IsSubterm t t
  | become {α : Eventuality} {u : Template α} {t : Template .state} :
      IsSubterm u t → IsSubterm u (become t)
  | causing {α β : Eventuality} {u : Template α} {c : Template .event} {e : Template β} :
      IsSubterm u c → IsSubterm u (cause c e)
  | caused {α β : Eventuality} {u : Template α} {c : Template .event} {e : Template β} :
      IsSubterm u e → IsSubterm u (cause c e)

/-- A template with a manner and a state has `CAUSE`. -/
theorem cause_mem_kinds_of_manner_of_state {t : Template σ} (hm : .manner ∈ t.kinds)
    (hs : .state ∈ t.kinds) : .cause ∈ t.kinds := by
  induction t with
  | state | act | effector => simp at hm hs
  | become _ ih =>
    simp only [kinds, Finset.mem_insert, reduceCtorEq, false_or] at hm hs ⊢
    exact ih hm hs
  | cause => simp

/-- The kinds of a subterm are among the kinds of the template. -/
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
