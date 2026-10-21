module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation

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
with an individual causer, which is the `vcause` of Beavers and Koontz-Garboden.

Templates are sorted like the domain of an `Interpretation`: `BECOME` turns a state template into
an event template and `CAUSE` relates two event templates. `Template.denote` interprets a
template with a root in its slots, the root's state predicate at the state and its manner at
`ACT`, through the heads `vBecome` and `vCause`. The primitives are the four kinds of entailment
of the root typology of Beavers and Koontz-Garboden, so `Template.kinds` reads a template's
primitives as a root signature, and membership in it is exactly what every denotation of the
template entails: a change for `HasResultState`, a causal relation for `HasCause`. A template's
denotation entails that each of its subterms is realized, which orders the readings of a
modifier such as *again* attached at different subterms.

## Main definitions

* `Eventuality`, `Template`: the two sorts, and the sorted terms, with `Template.achievement`
  and `Template.accomplishment`
* `Template.denote`: the denotation in an interpretation
* `Template.kinds`, `Template.HasCause`, `Template.HasResultState`
* `Template.causing`, `Template.caused`: the two subevents of a causative template
* `Template.IsSubterm`

## Main results

* `Template.hasResultState_iff`, `Template.hasCause_iff`: the diagnostics are the entailments
  of the denotation
* `Template.hasCause_of_mem_kinds`: a template with a manner and a state has `CAUSE`
* `Template.exists_denote_of_isSubterm`: a template's subterms are realized with its undergoer
* `Template.IsSubterm.kinds_subset`: a subterm's primitives are among the template's
* `Template.denote_cause_effector`: CAUSE with an individual causer is the effector of a
  `vCause` event

## Implementation notes

A template relates two participants, the actor `y`, which is the effector of an action and of a
causing subevent, and the undergoer `x`, of which the state holds. The caused subevent of
`CAUSE` is predicated of the undergoer, which is its actor when the caused subevent is itself
an action or a causation. An individual causer is the leaf `effector`, an eventuality with the
actor as its effector and no further content, so that `CAUSE` always relates two subevents. A
root has one manner, which every `ACT` of the template carries. The carriers of the two sorts
share a universe, so that the type of a denotation can depend on the sort.

## References

* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

open Semantics
open scoped SetRel

universe u

/-- The two sorts of eventuality a template describes. -/
inductive Eventuality where
  | state
  | event
  deriving DecidableEq, Repr

/-- The carrier of a sort, the states or the events of an interpretation. -/
abbrev Eventuality.Carrier (State Event : Type u) : Eventuality → Type u
  | .state => State
  | .event => Event

instance {State Event : Type u} [Nonempty State] [Nonempty Event] (σ : Eventuality) :
    Nonempty (σ.Carrier State Event) := by
  cases σ <;> assumption

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
  /-- `[causing CAUSE caused]`. -/
  | cause (causing caused : Template .event) : Template .event

namespace Template

variable {σ τ : Eventuality}

/-- The achievement `[BECOME [x ⟨STATE⟩]]`. -/
def achievement : Template .event := become state

/-- The accomplishment `[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`. -/
def accomplishment : Template .event := cause act achievement

/-- The kinds of entailment a template's primitives contribute: a state, the manner of an
action, the change of `BECOME` and the causation of `CAUSE`. -/
def kinds : {σ : Eventuality} → Template σ → Root.Kinds
  | _, state => {.state}
  | _, act => {.manner}
  | _, effector => ∅
  | _, become t => insert .result t.kinds
  | _, cause c e => insert .cause (c.kinds ∪ e.kinds)

/-- The template has `CAUSE`. -/
def HasCause (t : Template σ) : Prop := Root.Kind.cause ∈ t.kinds

/-- The template has `BECOME`, and so a result state. -/
def HasResultState (t : Template σ) : Prop := Root.Kind.result ∈ t.kinds

instance (t : Template σ) : Decidable t.HasCause := inferInstanceAs (Decidable (_ ∈ _))

instance (t : Template σ) : Decidable t.HasResultState := inferInstanceAs (Decidable (_ ∈ _))

/-- The causing subevent of a causative template. -/
def causing : Template .event → Option (Template .event)
  | cause c _ => some c
  | _ => none

/-- The caused subevent of a causative template. -/
def caused : Template .event → Option (Template .event)
  | cause _ e => some e
  | _ => none

/-- `u` occurs in `t`. -/
inductive IsSubterm : {α β : Eventuality} → Template α → Template β → Prop
  | refl {α : Eventuality} (t : Template α) : IsSubterm t t
  | become {α : Eventuality} {u : Template α} {t : Template .state} :
      IsSubterm u t → IsSubterm u (become t)
  | causing {α : Eventuality} {u : Template α} {c e : Template .event} :
      IsSubterm u c → IsSubterm u (cause c e)
  | caused {α : Eventuality} {u : Template α} {c e : Template .event} :
      IsSubterm u e → IsSubterm u (cause c e)

/-- A template whose primitives include a manner and a state has `CAUSE`, since causation is
the only primitive that relates an action to a state. -/
theorem hasCause_of_mem_kinds {t : Template σ} (hm : Root.Kind.manner ∈ t.kinds)
    (hs : Root.Kind.state ∈ t.kinds) : t.HasCause := by
  induction t with
  | state | act | effector => simp [kinds] at hm hs
  | become _ ih =>
    simp only [kinds, Finset.mem_insert, reduceCtorEq, false_or] at hm hs
    exact Finset.mem_insert_of_mem (ih hm hs)
  | cause => exact Finset.mem_insert_self _ _

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

/-! ### Denotation -/

section Denotation

variable {Entity : Type*} {State Event : Type u} (M : Interpretation Entity State Event)
  (P : Entity → State → Prop) (Q : Event → Prop)

/-- The denotation of a template in `M`, with a root's state predicate `P` at the state and its
manner `Q` at `ACT`: a relation between the actor, the undergoer and an eventuality of the
template's sort. -/
def denote : {σ : Eventuality} → Template σ → Entity → Entity → σ.Carrier State Event → Prop
  | _, state, _, x, s => P x s
  | _, act, y, _, v => M.effector y v ∧ Q v
  | _, effector, y, _, v => M.effector y v
  | _, become t, y, x, e => M.vBecome (fun x ↦ denote t y x) x e
  | _, cause c t, y, x, v => denote c y x v ∧ M.vCause (denote t x x) v

variable {M P Q} {y x : Entity}

/-- CAUSE with an individual causer is the `vcause` of Beavers and Koontz-Garboden, an event
whose effector is the causer and which causes the caused subevent. -/
theorem denote_cause_effector {t : Template .event} {v : Event} :
    (cause effector t).denote M P Q y x v ↔ M.effector y v ∧ M.vCause (t.denote M P Q x x) v :=
  Iff.rfl

/-- A template's denotation entails that each of its subterms is realized, with the same
undergoer. -/
theorem exists_denote_of_isSubterm {u : Template τ} {t : Template σ} (hu : u.IsSubterm t)
    {v : σ.Carrier State Event} (h : t.denote M P Q y x v) :
    ∃ y' w, u.denote M P Q y' x w := by
  induction hu generalizing y with
  | refl => exact ⟨y, v, h⟩
  | become _ ih => obtain ⟨_, _, hs⟩ := h; exact ih hs
  | causing _ ih => exact ih h.1
  | caused _ ih => obtain ⟨_, _, _, he⟩ := h; exact ih he

/-- A template with `BECOME` describes only eventualities that involve a change. -/
theorem exists_become_of_denote {t : Template σ} (ht : t.HasResultState)
    {v : σ.Carrier State Event} (h : t.denote M P Q y x v) : ∃ s e, s ~[M.become] e := by
  induction t generalizing y x with
  | state | act | effector => simp [HasResultState, kinds] at ht
  | become _ _ => obtain ⟨s, hb, _⟩ := h; exact ⟨s, _, hb⟩
  | cause c e ihc ihe =>
    simp only [HasResultState, kinds, Finset.mem_insert, Finset.mem_union, reduceCtorEq,
      false_or] at ht
    obtain ⟨hc, _, _, he⟩ := h
    exact ht.elim (ihc · hc) (ihe · he)

/-- A template with `CAUSE` describes only eventualities that involve a causal relation. -/
theorem exists_cause_of_denote {t : Template σ} (ht : t.HasCause)
    {v : σ.Carrier State Event} (h : t.denote M P Q y x v) : ∃ v e, v ~[M.cause] e := by
  induction t generalizing y x with
  | state | act | effector => simp [HasCause, kinds] at ht
  | become t ih =>
    simp only [HasCause, kinds, Finset.mem_insert, reduceCtorEq, false_or] at ht
    obtain ⟨_, _, hs⟩ := h
    exact ih ht hs
  | cause _ _ _ _ => obtain ⟨_, _, hc, _⟩ := h; exact ⟨_, _, hc⟩

end Denotation

/-! ### Completeness of the diagnostics -/

section Completeness

variable {Entity : Type*} {State Event : Type u}

/-- The interpretation in which every eventuality has every effector and causes every other,
and nothing gives rise to a state. -/
private def noChange (Entity : Type*) (State Event : Type u) :
    Interpretation Entity State Event where
  become := ⊥
  cause := ⊤
  effector := ⊤

/-- The interpretation in which every eventuality has every effector and gives rise to every
state, and nothing causes anything. -/
private def noCause (Entity : Type*) (State Event : Type u) :
    Interpretation Entity State Event where
  become := ⊤
  cause := ⊥
  effector := ⊤

private theorem denote_noChange [Nonempty Event] {t : Template σ} (ht : ¬ t.HasResultState)
    (y x : Entity) (v : σ.Carrier State Event) :
    t.denote (noChange Entity State Event) ⊤ ⊤ y x v := by
  induction t generalizing y x with
  | state | effector => trivial
  | act => exact ⟨trivial, trivial⟩
  | become _ _ => exact absurd (Finset.mem_insert_self _ _) ht
  | cause c e ihc ihe =>
    simp only [HasResultState, kinds, Finset.mem_insert, Finset.mem_union, reduceCtorEq,
      false_or, not_or] at ht
    exact ⟨ihc ht.1 y x v, Classical.arbitrary Event, trivial, ihe ht.2 x x _⟩

private theorem denote_noCause [Nonempty State] {t : Template σ} (ht : ¬ t.HasCause)
    (y x : Entity) (v : σ.Carrier State Event) :
    t.denote (noCause Entity State Event) ⊤ ⊤ y x v := by
  induction t generalizing y x with
  | state | effector => trivial
  | act => exact ⟨trivial, trivial⟩
  | become t ih =>
    simp only [HasCause, kinds, Finset.mem_insert, reduceCtorEq, false_or] at ht
    exact ⟨Classical.arbitrary State, trivial, ih ht y x _⟩
  | cause _ _ _ _ => exact absurd (Finset.mem_insert_self _ _) ht

variable [Nonempty Entity] [Nonempty State] [Nonempty Event] {t : Template σ}

/-- A template has `BECOME` iff every denotation of it, in every interpretation, involves a
change. -/
theorem hasResultState_iff :
    t.HasResultState ↔ ∀ (M : Interpretation Entity State Event) P Q y x
      (v : σ.Carrier State Event), t.denote M P Q y x v → ∃ s e, s ~[M.become] e := by
  refine ⟨fun ht _ _ _ _ _ _ ↦ exists_become_of_denote ht, fun h ↦ by_contra fun ht ↦ ?_⟩
  obtain ⟨_, _, hb⟩ := h _ _ _ (Classical.arbitrary _) (Classical.arbitrary _)
    (Classical.arbitrary _) (denote_noChange ht _ _ _)
  exact hb

/-- A template has `CAUSE` iff every denotation of it, in every interpretation, involves a
causal relation. -/
theorem hasCause_iff :
    t.HasCause ↔ ∀ (M : Interpretation Entity State Event) P Q y x
      (v : σ.Carrier State Event), t.denote M P Q y x v → ∃ v e, v ~[M.cause] e := by
  refine ⟨fun ht _ _ _ _ _ _ ↦ exists_cause_of_denote ht, fun h ↦ by_contra fun ht ↦ ?_⟩
  obtain ⟨_, _, hc⟩ := h _ _ _ (Classical.arbitrary _) (Classical.arbitrary _)
    (Classical.arbitrary _) (denote_noCause ht _ _ _)
  exact hc

end Completeness

end Template

end ArgumentStructure.EventStructure
