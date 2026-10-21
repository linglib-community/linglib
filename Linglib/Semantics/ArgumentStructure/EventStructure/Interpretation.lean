module

public import Linglib.Semantics.Root.Kinds

/-!
# Interpretations of the event-structure primitives

This file defines the interpretations of the primitives of event-structural decomposition. An
interpretation gives the three relations that the verbal heads introduce: an eventuality gives
rise to a state, an eventuality causes another, and an individual is the effector of an
eventuality. In the vocabulary of model theory it is a structure for the signature with these
three relation symbols, over the sorts of individuals, states and eventualities. The heads
themselves are operators on predicates. `vBecome` turns a state predicate into the predicate of
the events that give rise to such a state, and `vCause` turns an event predicate into the
predicate of the events that cause such an event.

A state predicate may itself entail a change or a cause of the change, and a manner predicate
describes actions. These are the meaning postulates that Beavers and Koontz-Garboden attach to
a root, one for each kind of entailment, with one more for a root that carries both a manner and
a cause, whose manner is that of the causing event. The postulates of a kind signature form a
theory, and an interpretation `Respects` the signature for a predicate when it is a model of
that theory. An entailment is then a statement about every interpretation, and a failure of
entailment is witnessed by one.

## Main definitions

* `EventStructure.Interpretation`: the relations `become`, `cause` and `effector`.
* `Interpretation.vBecome`, `Interpretation.vCause`: the two heads.
* `Interpretation.EntailsChange`, `EntailsCause`: the postulates on a state predicate.
* `Interpretation.EntailsManner`, `EntailsMannerOfCause`: a manner describes actions, and is the
  manner of the cause of a change.
* `Interpretation.Respects`: the interpretation is a model of the postulates of a signature.

## Main results

* `Interpretation.Entails.anti`, `Interpretation.isLowerSet_setOf_entails`: the postulates are
  downward closed along the order on kinds.
* `Interpretation.respects_close`: a signature and its collocational closure have the same
  models.

## Implementation notes

The sorts are type parameters, so a relation cannot be applied to an argument of the wrong sort.
mathlib's first-order structures are single-sorted; a view of an interpretation as such a
structure, with the postulates as sentences, is not yet defined.

## References

* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

/-- An interpretation of the event-structure primitives, the relations that the verbal heads
introduce. -/
structure Interpretation (Entity State Event : Type*) where
  /-- The eventuality gives rise to the state. -/
  become : State → Event → Prop
  /-- The first eventuality causes the second. -/
  cause : Event → Event → Prop
  /-- The individual is the effector of the eventuality. -/
  effector : Entity → Event → Prop

namespace Interpretation

variable {Entity State Event : Type*} (M : Interpretation Entity State Event)
  {P P' : Entity → State → Prop} {Q Q' : Event → Prop} {x y : Entity} {e : Event}

/-- The change-of-state head `vBecome P x` holds of the events that give rise to a state of
which `P x` holds. -/
def vBecome (P : Entity → State → Prop) (x : Entity) (e : Event) : Prop :=
  ∃ s, M.become s e ∧ P x s

/-- The causative head `vCause Q` holds of the eventualities that cause an eventuality of which
`Q` holds. It introduces no individual. -/
def vCause (Q : Event → Prop) (v : Event) : Prop :=
  ∃ e, M.cause v e ∧ Q e

variable {M}

theorem vBecome_mono (h : P ≤ P') : M.vBecome P ≤ M.vBecome P' :=
  fun x _ ⟨s, hb, hP⟩ ↦ ⟨s, hb, h x s hP⟩

theorem vCause_mono (h : Q ≤ Q') : M.vCause Q ≤ M.vCause Q' :=
  fun _ ⟨e, hc, hQ⟩ ↦ ⟨e, hc, h e hQ⟩

/-- A change gives rise to a state of the predicate. -/
theorem exists_state_of_vBecome (h : M.vBecome P x e) : ∃ s, M.become s e ∧ P x s := h

/-- A causing event has a caused event of the embedded predicate. -/
theorem exists_of_vCause (h : M.vCause Q e) : ∃ e', Q e' :=
  let ⟨e', _, hQ⟩ := h; ⟨e', hQ⟩

/-! ### Meaning postulates on a state predicate -/

section Postulates

open Semantics

variable (M) (P : Entity → State → Prop) (Q : Event → Prop) {ks : Root.Kinds}

/-- The state predicate `P` entails change when every state of which it holds arises from a
change. -/
def EntailsChange : Prop := ∀ x s, P x s → ∃ e, M.become s e

/-- The state predicate `P` entails a cause when every state of which it holds arises from a
change that some event causes. -/
def EntailsCause : Prop := ∀ x s, P x s → ∃ e v, M.become s e ∧ M.cause v e

/-- The manner `Q` describes actions, the book's feature (11b): every eventuality of the manner
has an effector. -/
def EntailsManner : Prop := ∀ v, Q v → ∃ y, M.effector y v

/-- The manner `Q` is the manner of the cause of a change of state, as with √drown and √hand, when
every state of which `P` holds arises from a change whose every cause is a `Q`-event. -/
def EntailsMannerOfCause : Prop := ∀ x s, P x s → ∃ e, M.become s e ∧ ∀ v, M.cause v e → Q v

/-- The meaning postulate of a kind of root entailment for the state predicate `P`, with `Q` the
manner. A state imposes nothing beyond the predicate itself. -/
def Entails : Root.Kind → Prop
  | .state => True
  | .result => M.EntailsChange P
  | .cause => M.EntailsCause P
  | .manner => M.EntailsManner Q

/-- The interpretation respects the kind signature `ks` for `P` and `Q` when it is a model of the
postulates of its kinds, and of the manner of the cause where `ks` has both. -/
def Respects (ks : Root.Kinds) : Prop :=
  (∀ k ∈ ks, M.Entails P Q k) ∧
    (Root.Kind.manner ∈ ks → Root.Kind.cause ∈ ks → M.EntailsMannerOfCause P Q)

variable {M P Q}

theorem EntailsCause.entailsChange (h : M.EntailsCause P) : M.EntailsChange P :=
  fun x s hs ↦ let ⟨e, _, hb, _⟩ := h x s hs; ⟨e, hb⟩

theorem EntailsMannerOfCause.entailsChange (h : M.EntailsMannerOfCause P Q) :
    M.EntailsChange P :=
  fun x s hs ↦ let ⟨e, hb, _⟩ := h x s hs; ⟨e, hb⟩

/-- The postulates are downward closed along the collocational order on kinds, since a cause
entails a change and both entail a state. -/
theorem Entails.anti {j k : Root.Kind} (hkj : k ≤ j) (h : M.Entails P Q j) :
    M.Entails P Q k := by
  cases hkj with
  | refl => exact h
  | state_result | state_cause => trivial
  | result_cause => exact EntailsCause.entailsChange h

variable (M P Q) in
/-- The kinds whose postulates hold form a lower set of the collocational order. -/
theorem isLowerSet_setOf_entails : IsLowerSet {k | M.Entails P Q k} :=
  fun _ _ hkj h ↦ Entails.anti hkj h

theorem respects_iff_subset : M.Respects P Q ks ↔ (ks : Set Root.Kind) ⊆ {k | M.Entails P Q k} ∧
    (Root.Kind.manner ∈ ks → Root.Kind.cause ∈ ks → M.EntailsMannerOfCause P Q) :=
  Iff.rfl

theorem Respects.mono {ks' : Root.Kinds} (hks : ks ⊆ ks') (h : M.Respects P Q ks') :
    M.Respects P Q ks :=
  ⟨fun k hk ↦ h.1 k (hks hk), fun hm hc ↦ h.2 (hks hm) (hks hc)⟩

/-- A signature is respected iff its collocational closure is, since the respected kinds form
a lower set and the closure adds no manner or cause. -/
@[simp] theorem respects_close : M.Respects P Q (Root.Kinds.close ks) ↔ M.Respects P Q ks := by
  simp only [respects_iff_subset, Root.Kinds.coe_close,
    Root.Kinds.mem_close_iff_of_isMax Root.Kind.isMax_manner,
    Root.Kinds.mem_close_iff_of_isMax Root.Kind.isMax_cause]
  exact and_congr_left' (lowerClosure_le (t := ⟨_, isLowerSet_setOf_entails M P Q⟩))

/-- An interpretation that respects a signature whose closure has a result satisfies the
postulate of change. -/
theorem Respects.entailsChange (h : M.Respects P Q ks)
    (hr : Root.Kind.result ∈ Root.Kinds.close ks) : M.EntailsChange P :=
  (respects_close.2 h).1 _ hr

end Postulates

end Interpretation

end ArgumentStructure.EventStructure
