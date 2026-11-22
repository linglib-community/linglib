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
`ACT`, with `BECOME` and `CAUSE` as possibility along the two relations and a thematic relation
`θ` between an actor and its eventuality; with an individual causer, `CAUSE` is an eventuality
that has the causer as its actor and causes the caused subevent
(`Template.denote_cause_effector`). The primitives are the four kinds of entailment of the root
typology of Beavers and Koontz-Garboden, so `Template.kinds` reads a template's primitives as a
root signature. A template whose primitives include a manner and a state has `CAUSE`
(`Template.cause_mem_kinds_of_manner_of_state`), and a subterm's primitives are among the
template's (`Template.IsSubterm.kinds_subset`). Membership in the signature is exactly what
every denotation of the template entails: it has a result iff every denotation involves a change
(`Template.result_mem_kinds_iff`), and a cause iff every denotation involves a causal relation
(`Template.cause_mem_kinds_iff`). A template's denotation entails that each of its subterms is
realized (`Template.exists_denote_of_isSubterm`), which orders the readings of a modifier such
as *again* attached at different subterms.

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

/-! ### Denotation -/

section Denotation

open ModalLogic

variable {Entity : Type*} {State Event : Type u} (M : Interpretation State Event)
  (θ : Entity → Event → Prop) (P : Entity → State → Prop) (Q : Event → Prop)

/-- The denotation of a template in `M`, with `θ` the relation of an actor to its eventuality, a
root's state predicate `P` at the state and its manner `Q` at `ACT`: a relation between the
actor, the undergoer and an eventuality of the template's sort. -/
def denote : {σ : Eventuality} → Template σ → Entity → Entity → σ.Carrier State Event → Prop
  | _, state, _, x, s => P x s
  | _, act, y, _, v => θ y v ∧ Q v
  | _, effector, y, _, v => θ y v
  | _, become t, y, x, e => ◇[M.become] (denote t y x) e
  | _, cause c t, y, x, v => denote c y x v ∧ ◇[M.cause] (denote t x x) v

variable {M θ P Q} {y x : Entity}

/-- A template's denotation grows with the relations of the interpretation. -/
theorem denote_mono {σ : Eventuality} (t : Template σ) (y x : Entity) :
    Monotone fun M : Interpretation State Event ↦ t.denote M θ P Q y x := by
  intro M N h
  induction t generalizing y x with
  | state | act | effector => exact le_rfl
  | become t ih => exact fun _ ⟨s, hs, hp⟩ ↦ ⟨s, h.1 hs, ih y x s hp⟩
  | cause c t ihc iht => exact fun _ ⟨hv, e, he, hp⟩ ↦ ⟨ihc y x _ hv, e, h.2 he, iht x x e hp⟩

/-- CAUSE with an individual causer is the `vcause` of Beavers and Koontz-Garboden, an event
whose effector is the causer and which causes the caused subevent. -/
theorem denote_cause_effector {t : Template .event} {v : Event} :
    (cause effector t).denote M θ P Q y x v ↔ θ y v ∧ ◇[M.cause] (t.denote M θ P Q x x) v :=
  Iff.rfl

/-- A template's denotation entails that each of its subterms is realized, with the same
undergoer. -/
theorem exists_denote_of_isSubterm {u : Template τ} {t : Template σ} (hu : u.IsSubterm t)
    {v : σ.Carrier State Event} (h : t.denote M θ P Q y x v) :
    ∃ y' w, u.denote M θ P Q y' x w := by
  induction hu generalizing y with
  | refl => exact ⟨y, v, h⟩
  | become _ ih => obtain ⟨_, _, hs⟩ := h; exact ih hs
  | causing _ ih => exact ih h.1
  | caused _ ih => obtain ⟨_, _, _, he⟩ := h; exact ih he

theorem exists_become_of_denote {t : Template σ} (ht : .result ∈ t.kinds)
    {v : σ.Carrier State Event} (h : t.denote M θ P Q y x v) : ∃ e s, e ~[M.become] s := by
  induction t generalizing y x with
  | state | act | effector => simp at ht
  | become _ _ => obtain ⟨s, hb, _⟩ := h; exact ⟨_, s, hb⟩
  | cause c e ihc ihe =>
    simp only [kinds, Finset.mem_insert, Finset.mem_union, reduceCtorEq, false_or] at ht
    obtain ⟨hc, _, _, he⟩ := h
    exact ht.elim (ihc · hc) (ihe · he)

theorem exists_cause_of_denote {t : Template σ} (ht : .cause ∈ t.kinds)
    {v : σ.Carrier State Event} (h : t.denote M θ P Q y x v) : ∃ v e, v ~[M.cause] e := by
  induction t generalizing y x with
  | state | act | effector => simp at ht
  | become t ih =>
    simp only [kinds, Finset.mem_insert, reduceCtorEq, false_or] at ht
    obtain ⟨_, _, hs⟩ := h
    exact ih ht hs
  | cause _ _ _ _ => obtain ⟨_, _, hc, _⟩ := h; exact ⟨_, _, hc⟩

/-- Where every individual is an actor of every eventuality, a template with the trivial state
and manner is realized everywhere, if every eventuality gives rise to a state when the template
has `BECOME` and causes an eventuality when it has `CAUSE`. -/
theorem denote_top (hθ : ∀ y v, θ y v) {t : Template σ}
    (hb : .result ∈ t.kinds → ∀ e, ∃ s, e ~[M.become] s)
    (hc : .cause ∈ t.kinds → ∀ v, ∃ e, v ~[M.cause] e) (y x : Entity)
    (v : σ.Carrier State Event) : t.denote M θ ⊤ ⊤ y x v := by
  induction t generalizing y x with
  | state => trivial
  | effector => exact hθ y v
  | act => exact ⟨hθ y v, trivial⟩
  | become t ih =>
    obtain ⟨s, hs⟩ := hb (by simp) v
    exact ⟨s, hs, ih (fun h ↦ hb (by simp [h])) (fun h ↦ hc (by simp [h])) y x s⟩
  | cause c e ihc ihe =>
    obtain ⟨e', he'⟩ := hc (by simp) v
    exact ⟨ihc (fun h ↦ hb (by simp [h])) (fun h ↦ hc (by simp [h])) y x v, e', he',
      ihe (fun h ↦ hb (by simp [h])) (fun h ↦ hc (by simp [h])) x x e'⟩

end Denotation

/-! ### Completeness of the signature -/

section Completeness

variable {Entity : Type*} {State Event : Type u} [Nonempty Entity] [Nonempty State]
  [Nonempty Event] {t : Template σ}

/-- A template has `BECOME` iff every denotation of it, in every interpretation, involves a
change. -/
theorem result_mem_kinds_iff :
    .result ∈ t.kinds ↔ ∀ (M : Interpretation State Event) (θ : Entity → Event → Prop) P Q y x
      (v : σ.Carrier State Event), t.denote M θ P Q y x v → ∃ e s, e ~[M.become] s := by
  refine ⟨fun ht _ _ _ _ _ _ _ ↦ exists_become_of_denote ht, fun h ↦ by_contra fun ht ↦ ?_⟩
  obtain ⟨_, _, hb⟩ := h ⟨⊥, ⊤⟩ ⊤ ⊤ ⊤ (Classical.arbitrary _) (Classical.arbitrary _)
    (Classical.arbitrary _)
    (denote_top (fun _ _ ↦ trivial) (fun hr ↦ absurd hr ht) (fun _ v ↦ ⟨v, trivial⟩) _ _ _)
  exact hb

/-- A template has `CAUSE` iff every denotation of it, in every interpretation, involves a
causal relation. -/
theorem cause_mem_kinds_iff :
    .cause ∈ t.kinds ↔ ∀ (M : Interpretation State Event) (θ : Entity → Event → Prop) P Q y x
      (v : σ.Carrier State Event), t.denote M θ P Q y x v → ∃ v e, v ~[M.cause] e := by
  refine ⟨fun ht _ _ _ _ _ _ _ ↦ exists_cause_of_denote ht, fun h ↦ by_contra fun ht ↦ ?_⟩
  obtain ⟨_, _, hc⟩ := h ⟨⊤, ⊥⟩ ⊤ ⊤ ⊤ (Classical.arbitrary _) (Classical.arbitrary _)
    (Classical.arbitrary _)
    (denote_top (fun _ _ ↦ trivial) (fun _ _ ↦ ⟨Classical.arbitrary _, trivial⟩)
      (fun hc ↦ absurd hc ht) _ _ _)
  exact hc

end Completeness

end Template

end ArgumentStructure.EventStructure
