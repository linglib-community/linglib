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

A state predicate may itself entail a change, a cause of the change, or a manner of the causing
event. These are the meaning postulates that Beavers and Koontz-Garboden attach to the state
predicate of a root, one for each kind of entailment. The postulates of a kind signature form a
theory, and an interpretation `Respects` the signature for a predicate when it is a model of
that theory. An entailment is then a statement about every interpretation, and a failure of
entailment is witnessed by one.

## Main definitions

* `EventStructure.Interpretation`: the relations `become`, `cause` and `effector`.
* `Interpretation.vBecome`, `Interpretation.vCause`: the two heads.
* `Interpretation.EntailsChange`, `EntailsCause`, `EntailsManner`: the postulates on a state
  predicate.
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

## TODO

The manner postulate is a condition on the state predicate and entails change
(`EntailsManner.entailsChange`), the manner of Beavers and Koontz-Garboden's √drown, which
restricts the cause of a change. For the pure manner signature of √jog it then requires every
state of the predicate to arise from a change, while the order on kinds keeps manner apart from
result, and the book's feature (11b) is that the root describes an action, a condition on the
event predicate `Q`. The two manners want separate postulates.

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

/-- The causative head `vCause Q y` holds of the events whose effector is `y` and which cause
an event of which `Q` holds. -/
def vCause (Q : Event → Prop) (y : Entity) (v : Event) : Prop :=
  ∃ e, M.effector y v ∧ M.cause v e ∧ Q e

variable {M}

theorem vBecome_mono (h : P ≤ P') : M.vBecome P ≤ M.vBecome P' :=
  fun x _ ⟨s, hb, hP⟩ ↦ ⟨s, hb, h x s hP⟩

theorem vCause_mono (h : Q ≤ Q') : M.vCause Q ≤ M.vCause Q' :=
  fun _ _ ⟨e, he, hc, hQ⟩ ↦ ⟨e, he, hc, h e hQ⟩

/-- A change gives rise to a state of the predicate. -/
theorem exists_state_of_vBecome (h : M.vBecome P x e) : ∃ s, M.become s e ∧ P x s := h

/-- A causing event has a caused event of the embedded predicate. -/
theorem exists_of_vCause (h : M.vCause Q y e) : ∃ e', Q e' :=
  let ⟨e', _, _, hQ⟩ := h; ⟨e', hQ⟩

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

/-- The state predicate `P` entails the manner `Q` when every state of which it holds arises
from a change whose every cause is a `Q`-event. -/
def EntailsManner : Prop := ∀ x s, P x s → ∃ e, M.become s e ∧ ∀ v, M.cause v e → Q v

/-- The meaning postulate of a kind of root entailment for the state predicate `P`, with `Q` the
manner. A state imposes nothing beyond the predicate itself. -/
def Entails : Root.Kind → Prop
  | .state => True
  | .result => M.EntailsChange P
  | .cause => M.EntailsCause P
  | .manner => M.EntailsManner P Q

/-- The interpretation respects the kind signature `ks` for `P` and `Q` when it is a model of the
postulates of its kinds. -/
def Respects (ks : Root.Kinds) : Prop := ∀ k ∈ ks, M.Entails P Q k

variable {M P Q}

theorem EntailsCause.entailsChange (h : M.EntailsCause P) : M.EntailsChange P :=
  fun x s hs ↦ let ⟨e, _, hb, _⟩ := h x s hs; ⟨e, hb⟩

theorem EntailsManner.entailsChange (h : M.EntailsManner P Q) : M.EntailsChange P :=
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

theorem respects_iff_subset : M.Respects P Q ks ↔ (ks : Set Root.Kind) ⊆ {k | M.Entails P Q k} :=
  Iff.rfl

theorem Respects.mono {ks' : Root.Kinds} (hks : ks ⊆ ks') (h : M.Respects P Q ks') :
    M.Respects P Q ks :=
  fun k hk ↦ h k (hks hk)

/-- A signature is respected iff its collocational closure is, since the respected kinds form
a lower set. -/
@[simp] theorem respects_close : M.Respects P Q (Root.Kinds.close ks) ↔ M.Respects P Q ks := by
  simp only [respects_iff_subset, Root.Kinds.coe_close]
  exact lowerClosure_le (t := ⟨_, isLowerSet_setOf_entails M P Q⟩)

/-- An interpretation that respects a signature whose closure has a result satisfies the
postulate of change. -/
theorem Respects.entailsChange (h : M.Respects P Q ks)
    (hr : Root.Kind.result ∈ Root.Kinds.close ks) : M.EntailsChange P :=
  respects_close.2 h _ hr

end Postulates

end Interpretation

end ArgumentStructure.EventStructure
