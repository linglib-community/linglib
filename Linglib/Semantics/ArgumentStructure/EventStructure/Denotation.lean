module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Model
public import Linglib.Semantics.ArgumentStructure.EventStructure.Template

/-!
# Denotations of event structure templates

This file interprets event structure templates in a model. Fix a model `M`, a thematic relation
`θ` between individuals and events, and the state predicate `P` and manner `Q` of a root.
`Template.denote` is then a relation between an actor `y`, an undergoer `x` and an eventuality:

* `state` holds of `s` when `P x s`;
* `act` holds of `v` when `θ y v` and `Q v`, and `effector` when `θ y v`;
* `become t` holds of `e` when `e` gives rise to a state of which `t` holds;
* `cause c t` holds of `v` when `c` holds of `v` and `v` causes an eventuality of which `t` holds
  with the undergoer as its actor.

The denotation is monotone in the model (`Template.denote_mono`) and entails that every subterm
is realized (`Template.exists_denote_of_isSubterm`). Giving the event of an individual causer a
manner yields the template with an action in its place (`Template.denote_cause_act`).

The kinds of a template are what all its denotations entail: it has `BECOME` iff every
denotation in every model involves a change (`Template.result_mem_kinds_iff`), and `CAUSE` iff
every denotation involves causation (`Template.cause_mem_kinds_iff`).

## Implementation notes

* The carriers of the two sorts share a universe, so that the type of a denotation can depend on
  the sort.
* A root has one manner, which every `act` of the template carries.

## References

* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

open scoped SetRel

universe u

/-- The carrier of a sort, the states or the events of a model. -/
abbrev Eventuality.Carrier (State Event : Type u) : Eventuality → Type u
  | .state => State
  | .event => Event

instance {State Event : Type u} [Nonempty State] [Nonempty Event] (σ : Eventuality) :
    Nonempty (σ.Carrier State Event) := by
  cases σ <;> assumption

/-- The causal relation of a model into a sort, `cause` into the events and
`causeState` into the states. -/
def Model.causeInto {State Event : Type u} (M : Model State Event) :
    (σ : Eventuality) → SetRel Event (σ.Carrier State Event)
  | .state => M.causeState
  | .event => M.cause

theorem Model.causeInto_mono {State Event : Type u} {M N : Model State Event}
    (h : M ≤ N) (σ : Eventuality) : M.causeInto σ ⊆ N.causeInto σ := by
  cases σ
  exacts [h.2.2, h.2.1]

namespace Template

variable {σ τ : Eventuality}

section Denotation

open ModalLogic

variable {Entity : Type*} {State Event : Type u} (M : Model State Event)
  (θ : Entity → Event → Prop) (P : Entity → State → Prop) (Q : Event → Prop)

/-- The denotation of a template in `M`, with `θ` the relation of an actor to its eventuality, a
root's state predicate `P` at the state and its manner `Q` at `ACT`: a relation between the
actor, the undergoer and an eventuality of the template's sort. -/
def denote : {σ : Eventuality} → Template σ → Entity → Entity → σ.Carrier State Event → Prop
  | _, state, _, x, s => P x s
  | _, act, y, _, v => θ y v ∧ Q v
  | _, effector, y, _, v => θ y v
  | _, become t, y, x, e => ◇[M.become] (denote t y x) e
  | _, cause (σ := τ) c t, y, x, v => denote c y x v ∧ ◇[M.causeInto τ] (denote t x x) v

variable {M θ P Q} {y x : Entity}

/-- A template's denotation grows with the relations of the model. -/
theorem denote_mono {σ : Eventuality} (t : Template σ) (y x : Entity) :
    Monotone fun M : Model State Event ↦ t.denote M θ P Q y x := by
  intro M N h
  induction t generalizing y x with
  | state | act | effector => exact le_rfl
  | become t ih => exact fun _ ⟨s, hs, hp⟩ ↦ ⟨s, h.1 hs, ih y x s hp⟩
  | cause c t ihc iht =>
    exact fun _ ⟨hv, e, he, hp⟩ ↦
      ⟨ihc y x _ hv, e, Model.causeInto_mono h _ he, iht x x e hp⟩

/-- CAUSE with an individual causer is the `vcause` of Beavers and Koontz-Garboden, an event
whose effector is the causer and which causes the caused subevent. -/
theorem denote_cause_effector {t : Template .event} {v : Event} :
    (cause effector t).denote M θ P Q y x v ↔ θ y v ∧ ◇[M.cause] (t.denote M θ P Q x x) v :=
  Iff.rfl

/-- Giving the eventuality of an individual causer a manner yields the template with an action
as its causing subevent. -/
theorem denote_cause_act {t : Template τ} {v : Event} :
    (cause act t).denote M θ P Q y x v ↔ (cause effector t).denote M θ P Q y x v ∧ Q v :=
  and_right_comm

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
    {v : σ.Carrier State Event} (h : t.denote M θ P Q y x v) :
    ∃ (τ : Eventuality) (v : Event) (e : τ.Carrier State Event), v ~[M.causeInto τ] e := by
  induction t generalizing y x with
  | state | act | effector => simp at ht
  | become t ih =>
    simp only [kinds, Finset.mem_insert, reduceCtorEq, false_or] at ht
    obtain ⟨_, _, hs⟩ := h
    exact ih ht hs
  | cause _ _ _ _ => obtain ⟨_, _, hc, _⟩ := h; exact ⟨_, _, _, hc⟩

/-- Where every individual is an actor of every eventuality, a template with the trivial state
and manner is realized everywhere, if every eventuality gives rise to a state when the template
has `BECOME` and causes an eventuality when it has `CAUSE`. -/
theorem denote_top (hθ : ∀ y v, θ y v) {t : Template σ}
    (hb : .result ∈ t.kinds → ∀ e, ∃ s, e ~[M.become] s)
    (hc : .cause ∈ t.kinds → ∀ (τ : Eventuality) (v : Event),
      ∃ e : τ.Carrier State Event, v ~[M.causeInto τ] e) (y x : Entity)
    (v : σ.Carrier State Event) : t.denote M θ ⊤ ⊤ y x v := by
  induction t generalizing y x with
  | state => trivial
  | effector => exact hθ y v
  | act => exact ⟨hθ y v, trivial⟩
  | become t ih =>
    obtain ⟨s, hs⟩ := hb (by simp) v
    exact ⟨s, hs, ih (fun h ↦ hb (by simp [h])) (fun h ↦ hc (by simp [h])) y x s⟩
  | cause c e ihc ihe =>
    obtain ⟨e', he'⟩ := hc (by simp) _ v
    exact ⟨ihc (fun h ↦ hb (by simp [h])) (fun h ↦ hc (by simp [h])) y x v, e', he',
      ihe (fun h ↦ hb (by simp [h])) (fun h ↦ hc (by simp [h])) x x e'⟩

end Denotation

/-! ### Completeness of the signature -/

section Completeness

variable {Entity : Type*} {State Event : Type u} [Nonempty Entity] [Nonempty State]
  [Nonempty Event] {t : Template σ}

/-- A template has `BECOME` iff every denotation of it, in every model, involves a
change. -/
theorem result_mem_kinds_iff :
    .result ∈ t.kinds ↔ ∀ (M : Model State Event) (θ : Entity → Event → Prop) P Q y x
      (v : σ.Carrier State Event), t.denote M θ P Q y x v → ∃ e s, e ~[M.become] s := by
  refine ⟨fun ht _ _ _ _ _ _ _ ↦ exists_become_of_denote ht, fun h ↦ by_contra fun ht ↦ ?_⟩
  obtain ⟨_, _, hb⟩ := h ⟨⊥, ⊤, ⊤⟩ ⊤ ⊤ ⊤ (Classical.arbitrary _) (Classical.arbitrary _)
    (Classical.arbitrary _)
    (denote_top (fun _ _ ↦ trivial) (fun hr ↦ absurd hr ht)
      (fun _ τ _ ↦ ⟨Classical.arbitrary _, by cases τ <;> trivial⟩) _ _ _)
  exact hb

/-- A template has `CAUSE` iff every denotation of it, in every model, involves a
causal relation. -/
theorem cause_mem_kinds_iff :
    .cause ∈ t.kinds ↔ ∀ (M : Model State Event) (θ : Entity → Event → Prop) P Q y x
      (v : σ.Carrier State Event), t.denote M θ P Q y x v →
        ∃ (τ : Eventuality) (v : Event) (e : τ.Carrier State Event), v ~[M.causeInto τ] e := by
  refine ⟨fun ht _ _ _ _ _ _ _ ↦ exists_cause_of_denote ht, fun h ↦ by_contra fun ht ↦ ?_⟩
  obtain ⟨τ, _, _, hc⟩ := h ⟨⊤, ⊥, ⊥⟩ ⊤ ⊤ ⊤ (Classical.arbitrary _) (Classical.arbitrary _)
    (Classical.arbitrary _)
    (denote_top (fun _ _ ↦ trivial) (fun _ _ ↦ ⟨Classical.arbitrary _, trivial⟩)
      (fun hc ↦ absurd hc ht) _ _ _)
  cases τ <;> exact hc

end Completeness

end Template

end ArgumentStructure.EventStructure
