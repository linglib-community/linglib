module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.ArgumentStructure.Root.Basic

/-!
# Interpretations of the event-structure primitives

Event-structural decomposition builds the meaning of a verb from three relations: a state `s`
*arises from* an eventuality `e`, written `s ~[become] e`, an eventuality `v` *causes* an
eventuality `e`, written `v ~[cause] e`, and an individual `y` is the *effector* of an
eventuality `v`. An `EventStructure.Interpretation` over types of individuals, states and
eventualities is a choice of these three relations.

The verbal heads are possibility operators along the relations. For a state predicate `P` and an
individual `x`, `vBecome P x` is the predicate `fun e ↦ ∃ s, s ~[become] e ∧ P x s` of the
eventualities that give rise to a `P`-state of `x`, and for a predicate `Q` of eventualities,
`vCause Q` is the predicate `fun v ↦ ∃ e, v ~[cause] e ∧ Q e` of the eventualities that cause a
`Q`-eventuality. Possibility along a relation is left adjoint to necessity along its converse, so
the eventualities that cause a change into a `P`-state all satisfy `Q` exactly when every cause
of every change that a `P`-state arises from does (`Interpretation.vCause_vBecome_le_iff`).

A root's state predicate `p` and manner predicate `Q` may carry entailments of their own, the
meaning postulates of Beavers and Koontz-Garboden. `p` *entails change* when every `p`-state
arises from some change, `p ≤ ◇[become] ⊤`, and *entails a cause* when that change has a
cause, `p ≤ ◇[become] (◇[cause.inv] ⊤)`. `Q` *is a manner* when every `Q`-eventuality has an
effector, and `Q` *is the manner of the cause* of `p` when every `p`-state arises from a change
that has a cause and whose causes are all `Q`-eventualities,
`p ≤ ◇[become] (◇[cause.inv] ⊤ ⊓ □[cause.inv] Q)`. An interpretation `Respects` a kind
signature for `p` and `Q` when the postulates of the kinds in the signature hold. Each postulate
entails the one before it, so a signature and its collocational closure have the same models
(`Interpretation.respects_close`). Where a state arises from at most one change, the manner of
the cause holds of the causing event of the causative
(`Interpretation.EntailsMannerOfCause.vCause_vBecome_le`).

## Implementation notes

The sorts are type parameters, so a relation cannot be applied to an argument of the wrong sort;
mathlib's `FirstOrder.Language.Structure` is single-sorted and would need sort predicates and a
relativized quantifier in each postulate.

`vCause` introduces no individual. The causative head of [beavers-koontz-garboden-2020] also
makes its subject the effector of the causing eventuality, which a caller states as a conjunct
(`Template.denote` at `Template.effector`), so that the same operator serves analyses on which
the causer is introduced by a separate head.

The effector relation is curried, like the thematic relations of
`ArgumentStructure.ThematicFrame`, where `become` and `cause` are sets of pairs along which the
modal operators are taken.

## TODO

* `EntailsMannerOfCause` is the postulate of a root in the complement of `v`, whose state
  predicate constrains the cause. A manner root adjoined to `v` that carries a cause, such as
  √hand, has the converse postulate, on which every eventuality of the manner causes a change;
  it is not defined, and `Respects` does not read the root's position.

## References

* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

/-- An interpretation of the event-structure primitives, the relations that the verbal heads
introduce. -/
@[ext]
structure Interpretation (Entity State Event : Type*) where
  /-- A state and the eventuality that gives rise to it. -/
  become : SetRel State Event
  /-- An eventuality and an eventuality it causes. -/
  cause : SetRel Event Event
  /-- The individual is the effector of the eventuality. -/
  effector : Entity → Event → Prop

namespace Interpretation

open ModalLogic
open scoped SetRel

variable {Entity State Event : Type*} (M : Interpretation Entity State Event)
  {P P' : Entity → State → Prop} {Q Q' : Event → Prop} {x : Entity} {s : State} {e v : Event}

/-- The change-of-state head `vBecome P x` holds of the events that give rise to a state of
which `P x` holds. -/
def vBecome (P : Entity → State → Prop) (x : Entity) : Event → Prop := ◇[M.become.inv] (P x)

/-- The causative head `vCause Q` holds of the eventualities that cause an eventuality of which
`Q` holds. -/
def vCause (Q : Event → Prop) : Event → Prop := ◇[M.cause] Q

variable {M}

theorem vBecome_iff : M.vBecome P x e ↔ ∃ s, s ~[M.become] e ∧ P x s := .rfl

theorem vCause_iff : M.vCause Q v ↔ ∃ e, v ~[M.cause] e ∧ Q e := .rfl

@[gcongr]
theorem vBecome_mono (h : P ≤ P') : M.vBecome P ≤ M.vBecome P' :=
  fun x ↦ diamond_mono _ (h x)

@[gcongr]
theorem vCause_mono (h : Q ≤ Q') : M.vCause Q ≤ M.vCause Q' :=
  diamond_mono _ h

/-- The eventualities that cause a change into a `P`-state of `x` all satisfy `Q` iff every
cause of every change that a `P`-state of `x` arises from does. -/
theorem vCause_vBecome_le_iff :
    M.vCause (M.vBecome P x) ≤ Q ↔ P x ≤ □[M.become] (□[M.cause.inv] Q) :=
  (diamond_box_gc M.cause _ _).trans (diamond_box_gc M.become.inv _ _)

/-! ### Meaning postulates -/

section Postulates

variable (M) (p : State → Prop) (Q : Event → Prop) {ks ks' : Finset Root.Kind}

/-- The state predicate `p` entails change when every state of which it holds arises from a
change. -/
def EntailsChange : Prop := p ≤ ◇[M.become] ⊤

/-- The state predicate `p` entails a cause when every state of which it holds arises from a
change that some eventuality causes. -/
def EntailsCause : Prop := p ≤ ◇[M.become] (◇[M.cause.inv] ⊤)

/-- `Q` is a manner when it describes actions: every eventuality of which it holds has an
effector. -/
def EntailsManner : Prop := ∀ v, Q v → ∃ y, M.effector y v

/-- `Q` is the manner of the cause of `p`, as with √guillotine and √drown, when every state of
which `p` holds arises from a change that has a cause and whose every cause is a
`Q`-eventuality. -/
def EntailsMannerOfCause : Prop := p ≤ ◇[M.become] (◇[M.cause.inv] ⊤ ⊓ □[M.cause.inv] Q)

/-- The interpretation respects the kind signature `ks` for the state predicate `p` and the
manner `Q` when the meaning postulate of each kind in `ks` holds, and that of the manner of the
cause for a signature with a manner and a cause. The state kind imposes nothing beyond `p`. -/
@[mk_iff]
structure Respects (ks : Finset Root.Kind) : Prop where
  /-- A state of a result root arises from a change. -/
  change : .result ∈ ks → M.EntailsChange p
  /-- A state of a root with a cause arises from a caused change. -/
  cause : .cause ∈ ks → M.EntailsCause p
  /-- The manner of a manner root describes actions. -/
  manner : .manner ∈ ks → M.EntailsManner Q
  /-- The manner of a root with a manner and a cause is that of the cause of the change. -/
  mannerOfCause : .manner ∈ ks → .cause ∈ ks → M.EntailsMannerOfCause p Q

variable {M p Q}

theorem EntailsCause.entailsChange (h : M.EntailsCause p) : M.EntailsChange p :=
  h.trans (diamond_mono _ le_top)

theorem EntailsMannerOfCause.entailsCause (h : M.EntailsMannerOfCause p Q) : M.EntailsCause p :=
  h.trans (diamond_mono _ inf_le_left)

/-- A state of a root whose manner is that of the cause arises from a change that some
eventuality of the manner causes. -/
theorem EntailsMannerOfCause.le_diamond_diamond (h : M.EntailsMannerOfCause p Q) :
    p ≤ ◇[M.become] (◇[M.cause.inv] Q) :=
  h.trans <| diamond_mono _ fun _ ⟨⟨v, hv, _⟩, hQ⟩ ↦ ⟨v, hv, hQ v hv⟩

/-- A state of a root whose manner is that of the cause arises from a change caused by an
action of the manner, with an effector. -/
theorem EntailsMannerOfCause.exists_effector (h : M.EntailsMannerOfCause p Q)
    (hQ : M.EntailsManner Q) (hs : p s) :
    ∃ e v y, s ~[M.become] e ∧ v ~[M.cause] e ∧ Q v ∧ M.effector y v :=
  let ⟨e, he, v, hv, hQv⟩ := h.le_diamond_diamond s hs
  let ⟨y, hy⟩ := hQ v hQv
  ⟨e, v, y, he, hv, hQv, hy⟩

/-- Where a state arises from at most one change, the manner of the cause holds of every
eventuality that causes a change into a state of the root. -/
theorem EntailsMannerOfCause.vCause_vBecome_le (h : M.EntailsMannerOfCause (P x) Q)
    (hM : ∀ s ⦃e⦄, s ~[M.become] e → ∀ ⦃e'⦄, s ~[M.become] e' → e = e') :
    M.vCause (M.vBecome P x) ≤ Q :=
  vCause_vBecome_le_iff.2 <| h.trans <|
    (diamond_mono _ inf_le_right).trans (diamond_le_box_iff.2 hM _)

theorem Respects.mono (hks : ks ⊆ ks') (h : M.Respects p Q ks') : M.Respects p Q ks :=
  ⟨fun hk ↦ h.change (hks hk), fun hk ↦ h.cause (hks hk), fun hk ↦ h.manner (hks hk),
    fun hm hc ↦ h.mannerOfCause (hks hm) (hks hc)⟩

/-- A signature is respected iff its collocational closure is: the closure adds a result only
below a cause, whose postulate entails change, and adds no manner or cause. -/
@[simp] theorem respects_close : M.Respects p Q (Root.close ks) ↔ M.Respects p Q ks := by
  have hm := Root.mem_close_iff_of_isMax (r := ks) Root.Kind.isMax_manner
  have hc := Root.mem_close_iff_of_isMax (r := ks) Root.Kind.isMax_cause
  refine ⟨.mono (Root.close.le_closure ks), fun h ↦ ⟨fun hr ↦ ?_, fun hk ↦ h.cause (hc.1 hk),
    fun hk ↦ h.manner (hm.1 hk), fun hk hk' ↦ h.mannerOfCause (hm.1 hk) (hc.1 hk')⟩⟩
  obtain ⟨j, hj, hrj⟩ := Root.mem_close.1 hr
  cases hrj with
  | refl => exact h.change hj
  | result_cause => exact (h.cause hj).entailsChange

theorem Respects.entailsChange (h : M.Respects p Q ks)
    (hr : Root.Kind.result ∈ Root.close ks) : M.EntailsChange p :=
  (respects_close.2 h).change hr

end Postulates

end Interpretation

end ArgumentStructure.EventStructure
