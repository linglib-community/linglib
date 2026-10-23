module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Root.Kinds

/-!
# Interpretations of the event-structure primitives

This file defines the interpretations of the primitives of event-structural decomposition. An
interpretation gives the three relations that the verbal heads introduce: an eventuality gives
rise to a state, an eventuality causes another, and an individual is the effector of an
eventuality. In the vocabulary of model theory it is a structure for the signature with these
three relation symbols, over the sorts of individuals, states and eventualities. The heads
themselves are operators on predicates, possibility along the relations: `vBecome` turns a state
predicate into the predicate of the events that give rise to such a state, possibility along the
converse of `become`, and `vCause` turns an event predicate into the predicate of the events
that cause such an event, possibility along `cause`.

A state predicate may itself entail a change or a cause of the change, and a manner predicate
describes actions. These are the meaning postulates that Beavers and Koontz-Garboden attach to
a root, one for each kind of entailment, with one more for a root that carries both a manner and
a cause, whose manner is that of the causing event. The postulates of a kind signature form a
theory, and an interpretation `Respects` the signature for a predicate when it is a model of
that theory. The postulates are modal formulas over the same relations, so the entailments among
them are instances of the monotonicity of possibility. An entailment is then a statement about
every interpretation, and a failure of entailment is witnessed by one.

## Main definitions

* `EventStructure.Interpretation`: the relations `become`, `cause` and `effector`.
* `Interpretation.vBecome`, `Interpretation.vCause`: the two heads.
* `Interpretation.EntailsChange`, `EntailsCause`: the postulates on a state predicate.
* `Interpretation.EntailsManner`, `EntailsMannerOfCause`: a manner describes actions, and is the
  manner of the cause of a change.
* `EventStructure.Postulate`: the postulates of the theory, each with the kinds that trigger it.
* `Interpretation.Respects`: the interpretation is a model of the postulates a signature triggers.

## Main results

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
  /-- A state and the eventuality that gives rise to it. -/
  become : SetRel State Event
  /-- An eventuality and an eventuality it causes. -/
  cause : SetRel Event Event
  /-- The individual is the effector of the eventuality. -/
  effector : Entity → Event → Prop

/-- The meaning postulates of the root typology. -/
inductive Postulate
  /-- A state of the root arises from a change. -/
  | change
  /-- A state of the root arises from a caused change. -/
  | cause
  /-- The root's manner describes actions. -/
  | manner
  /-- The root's manner is that of the cause of the change. -/
  | mannerOfCause
  deriving DecidableEq, Fintype

/-- The kinds a signature carries when the postulate applies to it: a postulate for each kind
but the state, which imposes nothing beyond the predicate, and the manner of the cause for a
manner with a cause. -/
def Postulate.trigger : Postulate → Semantics.Root.Kinds
  | .change => {.result}
  | .cause => {.cause}
  | .manner => {.manner}
  | .mannerOfCause => {.manner, .cause}

namespace Interpretation

open ModalLogic
open scoped SetRel

variable {Entity State Event : Type*} (M : Interpretation Entity State Event)
  {P P' : Entity → State → Prop} {Q Q' : Event → Prop} {x y : Entity} {e : Event}

/-- The change-of-state head `vBecome P x` holds of the events that give rise to a state of
which `P x` holds. -/
def vBecome (P : Entity → State → Prop) (x : Entity) : Event → Prop := ◇[M.become.inv] (P x)

/-- The causative head `vCause Q` holds of the eventualities that cause an eventuality of which
`Q` holds. It introduces no individual. -/
def vCause (Q : Event → Prop) : Event → Prop := ◇[M.cause] Q

variable {M}

theorem vBecome_iff : M.vBecome P x e ↔ ∃ s, s ~[M.become] e ∧ P x s := .rfl

theorem vCause_iff : M.vCause Q e ↔ ∃ e', e ~[M.cause] e' ∧ Q e' := .rfl

theorem vBecome_mono (h : P ≤ P') : M.vBecome P ≤ M.vBecome P' :=
  fun x ↦ diamond_mono _ (h x)

theorem vCause_mono (h : Q ≤ Q') : M.vCause Q ≤ M.vCause Q' :=
  diamond_mono _ h

/-! ### Meaning postulates on a state predicate -/

section Postulates

open Semantics

variable (M) (P : Entity → State → Prop) (Q : Event → Prop) {ks : Root.Kinds}

/-- The state predicate `P` entails change when every state of which it holds arises from a
change. -/
def EntailsChange : Prop := ∀ x, P x ≤ ◇[M.become] ⊤

/-- The state predicate `P` entails a cause when every state of which it holds arises from a
change that some eventuality causes. -/
def EntailsCause : Prop := ∀ x, P x ≤ ◇[M.become] (◇[M.cause.inv] ⊤)

/-- The manner `Q` describes actions, the book's feature (11b): every eventuality of the manner
has an effector. -/
def EntailsManner : Prop := ∀ v, Q v → ∃ y, M.effector y v

/-- The manner `Q` is the manner of the cause of a change of state, as with √drown and √hand, when
every state of which `P` holds arises from a change whose every cause is a `Q`-eventuality. -/
def EntailsMannerOfCause : Prop := ∀ x, P x ≤ ◇[M.become] (□[M.cause.inv] Q)

/-- The postulate in `M` for the state predicate `P` and the manner `Q`. -/
def Holds : Postulate → Prop
  | .change => M.EntailsChange P
  | .cause => M.EntailsCause P
  | .manner => M.EntailsManner Q
  | .mannerOfCause => M.EntailsMannerOfCause P Q

/-- The interpretation respects the kind signature `ks` for `P` and `Q` when every postulate that
`ks` triggers holds. -/
def Respects (ks : Root.Kinds) : Prop := ∀ p : Postulate, p.trigger ⊆ ks → M.Holds P Q p

variable {M P Q}

theorem EntailsCause.entailsChange (h : M.EntailsCause P) : M.EntailsChange P :=
  fun x ↦ (h x).trans (diamond_mono _ le_top)

theorem EntailsMannerOfCause.entailsChange (h : M.EntailsMannerOfCause P Q) :
    M.EntailsChange P :=
  fun x ↦ (h x).trans (diamond_mono _ le_top)

theorem Respects.mono {ks' : Root.Kinds} (hks : ks ⊆ ks') (h : M.Respects P Q ks') :
    M.Respects P Q ks :=
  fun p hp ↦ h p (hp.trans hks)

/-- A signature is respected iff its collocational closure is: the closure adds a result only
below a cause, whose postulate entails change, and adds no manner or cause. -/
@[simp] theorem respects_close : M.Respects P Q (Root.Kinds.close ks) ↔ M.Respects P Q ks := by
  refine ⟨Respects.mono (Root.Kinds.close.le_closure ks), fun h p hp ↦ ?_⟩
  have hm := Root.Kinds.mem_close_iff_of_isMax (s := ks) Root.Kind.isMax_manner
  have hc := Root.Kinds.mem_close_iff_of_isMax (s := ks) Root.Kind.isMax_cause
  cases p with
  | change =>
    obtain ⟨j, hj, hrj⟩ := Root.Kinds.mem_close.1 (Finset.singleton_subset_iff.1 hp)
    cases hrj with
    | refl => exact h .change (Finset.singleton_subset_iff.2 hj)
    | result_cause => exact (h .cause (Finset.singleton_subset_iff.2 hj)).entailsChange
  | cause => exact h .cause (by simpa [Postulate.trigger, hc] using hp)
  | manner => exact h .manner (by simpa [Postulate.trigger, hm] using hp)
  | mannerOfCause =>
    exact h .mannerOfCause (by simpa [Postulate.trigger, Finset.insert_subset_iff, hm, hc] using hp)

theorem Respects.entailsChange (h : M.Respects P Q ks)
    (hr : Root.Kind.result ∈ Root.Kinds.close ks) : M.EntailsChange P :=
  respects_close.2 h .change (Finset.singleton_subset_iff.2 hr)

end Postulates

end Interpretation

end ArgumentStructure.EventStructure
