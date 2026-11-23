module

public import Linglib.Semantics.ArgumentStructure.Root.Basic

/-!
# Event structure templates

An event structure template is a term over a small set of primitive predicates: a state, an
action `ACT`, a change `BECOME` and causation `CAUSE`, where `BECOME` and `CAUSE` take templates
as arguments and so build larger templates out of smaller ones (Rappaport Hovav and Levin;
Beavers and Koontz-Garboden). A verb's meaning pairs a template, which fixes its class, with a
root, which tells it apart from the other members of the class. The basic inventory of
Rappaport Hovav and Levin is the state `[x ⟨STATE⟩]`, the activity `[x ACT⟨MANNER⟩]`, the
achievement `[BECOME [x ⟨STATE⟩]]` and the two accomplishments
`[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]` and `[x CAUSE [BECOME [y ⟨STATE⟩]]]`, the second
with an individual causer, which is the `vcause` of Beavers and Koontz-Garboden. `CAUSE` may also
take a state, `[x CAUSE [y ⟨STATE⟩]]`, a causative with no change.

Templates are sorted: `BECOME` turns a state template into an event template and `CAUSE` relates
an event template to a template of either sort. The primitives are the four kinds of entailment
of the root typology of Beavers and Koontz-Garboden, so `Template.kinds` reads a template's
primitives as a root signature. A template whose primitives include a manner and a state has
`CAUSE` (`Template.cause_mem_kinds_of_manner_of_state`), and a subterm's primitives are among the
template's (`Template.IsSubterm.kinds_subset`).

## Implementation notes

An individual causer is the leaf `effector`, an eventuality with no content beyond its effector,
so that `CAUSE` always relates two subevents.

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
