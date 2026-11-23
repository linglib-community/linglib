module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Model
public import Linglib.Semantics.ArgumentStructure.Root.Basic

/-!
# Meaning postulates of roots

This file defines the entailments that the predicates of a root may carry in a model of the
event-structure primitives, the meaning postulates of [beavers-koontz-garboden-2020]. For a
state predicate `p` and a manner predicate `Q`:

* `p` entails change when every `p`-state arises from a change, `p ≤ ◇[become.inv] ⊤`;
* `p` entails a cause when that change has a cause, `p ≤ ◇[become.inv] (◇[cause.inv] ⊤)`;
* `Q` is the manner of the cause of `p` when the change has a cause and every cause of it is a
  `Q`-event, `p ≤ ◇[become.inv] (◇[cause.inv] ⊤ ⊓ □[cause.inv] Q)`;
* `Q` entails the caused result `p` when every `Q`-event causes a change into a `p`-state,
  `Q ≤ ◇[cause] (◇[become] p)`.

A model `Respects` a kind signature when the postulates of its kinds hold. Each postulate entails
the one before it, so a signature and its closure have the same models (`Model.respects_close`).
Where a state arises from at most one change, `Q` is the manner of the cause of `p` iff `p`
entails a cause and every event that causes a change into a `p`-state is a `Q`-event
(`Model.entailsMannerOfCause_iff`).

## Implementation notes

* `Respects` reads a signature as the postulates of a root in the complement of `v`. For a root
  adjoined to `v` the cause kind is `EntailsCausedResult` of a result the signature does not fix,
  so a caller states that postulate of the result it means.
* The postulates concern caused changes and are stated of `cause`, not of `causeState`.

## References

* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure.Model

open ModalLogic
open scoped SetRel

variable {State Event : Type*} (M : Model State Event) (p : State → Prop)
  (Q : Event → Prop) {ks ks' : Finset Root.Kind}

/-- The state predicate `p` entails change when every state of which it holds arises from a
change. -/
def EntailsChange : Prop := p ≤ ◇[M.become.inv] ⊤

/-- The state predicate `p` entails a cause when every state of which it holds arises from a
change that some eventuality causes. -/
def EntailsCause : Prop := p ≤ ◇[M.become.inv] (◇[M.cause.inv] ⊤)

/-- `Q` is the manner of the cause of `p`, as with √guillotine and √drown, when every state of
which `p` holds arises from a change that has a cause and whose every cause is a
`Q`-eventuality. -/
def EntailsMannerOfCause : Prop :=
  p ≤ ◇[M.become.inv] (◇[M.cause.inv] ⊤ ⊓ □[M.cause.inv] Q)

/-- The manner `Q` entails the caused result `p`, as with √hand, when every eventuality of which
`Q` holds causes a change into a state of which `p` holds. -/
def EntailsCausedResult (M : Model State Event) (Q : Event → Prop)
    (p : State → Prop) : Prop :=
  Q ≤ ◇[M.cause] (◇[M.become] p)

/-- The model respects the kind signature `ks` for the state predicate `p` of a root
and the manner `Q` when the meaning postulate of each kind in `ks` holds of `p`, and that of the
manner of the cause for a signature with a manner and a cause. The state and manner kinds impose
nothing beyond the predicates. -/
@[mk_iff]
structure Respects (ks : Finset Root.Kind) : Prop where
  /-- A state of a result root arises from a change. -/
  change : .result ∈ ks → M.EntailsChange p
  /-- A state of a root with a cause arises from a caused change. -/
  cause : .cause ∈ ks → M.EntailsCause p
  /-- The manner of a root with a manner and a cause is that of the cause of the change. -/
  mannerOfCause : .manner ∈ ks → .cause ∈ ks → M.EntailsMannerOfCause p Q

variable {M p Q}

theorem EntailsCause.entailsChange (h : M.EntailsCause p) : M.EntailsChange p :=
  h.trans (diamond_mono _ le_top)

theorem EntailsMannerOfCause.entailsCause (h : M.EntailsMannerOfCause p Q) : M.EntailsCause p :=
  h.trans (diamond_mono _ inf_le_left)

/-- A state of a root whose manner is that of the cause arises from a change that some
eventuality of the manner causes. -/
theorem EntailsMannerOfCause.le_diamond_inv_diamond_inv (h : M.EntailsMannerOfCause p Q) :
    p ≤ ◇[M.become.inv] (◇[M.cause.inv] Q) :=
  h.trans <| diamond_mono _ fun _ ⟨⟨v, hv, _⟩, hQ⟩ ↦ ⟨v, hv, hQ v hv⟩

/-- Where a state arises from at most one change, the manner of the cause holds of every
eventuality that causes a change into a state of the root. -/
theorem EntailsMannerOfCause.diamond_cause_diamond_become_le (h : M.EntailsMannerOfCause p Q)
    (hM : ∀ s ⦃e⦄, e ~[M.become] s → ∀ ⦃e'⦄, e' ~[M.become] s → e = e') :
    ◇[M.cause] (◇[M.become] p) ≤ Q :=
  (diamond_box_gc M.cause _ _).2 <| (diamond_box_gc M.become _ _).2 <| h.trans <|
    (diamond_mono _ inf_le_right).trans (diamond_le_box_iff.2 hM _)

/-- A state predicate that entails a cause has `Q` as the manner of its cause if every
eventuality that causes a change into one of its states is a `Q`-eventuality. -/
theorem EntailsCause.entailsMannerOfCause (h : M.EntailsCause p)
    (hQ : ◇[M.cause] (◇[M.become] p) ≤ Q) : M.EntailsMannerOfCause p Q :=
  fun s hs ↦ let ⟨e, he, hc⟩ := h s hs; ⟨e, he, hc, fun v hv ↦ hQ v ⟨e, hv, s, he, hs⟩⟩

/-- Where a state arises from at most one change, `Q` is the manner of the cause of `p` iff `p`
entails a cause and every eventuality that causes a change into a `p`-state is a
`Q`-eventuality. -/
theorem entailsMannerOfCause_iff
    (hM : ∀ s ⦃e⦄, e ~[M.become] s → ∀ ⦃e'⦄, e' ~[M.become] s → e = e') :
    M.EntailsMannerOfCause p Q ↔ M.EntailsCause p ∧ ◇[M.cause] (◇[M.become] p) ≤ Q :=
  ⟨fun h ↦ ⟨h.entailsCause, h.diamond_cause_diamond_become_le hM⟩,
    fun h ↦ h.1.entailsMannerOfCause h.2⟩

theorem Respects.mono (hks : ks ⊆ ks') (h : M.Respects p Q ks') : M.Respects p Q ks :=
  ⟨fun hk ↦ h.change (hks hk), fun hk ↦ h.cause (hks hk),
    fun hm hc ↦ h.mannerOfCause (hks hm) (hks hc)⟩

/-- A signature is respected iff its collocational closure is: the closure adds a result only
below a cause, whose postulate entails change, and adds no manner or cause. -/
@[simp] theorem respects_close : M.Respects p Q (Root.close ks) ↔ M.Respects p Q ks := by
  have hm := Root.mem_close_iff_of_isMax (r := ks) Root.Kind.isMax_manner
  have hc := Root.mem_close_iff_of_isMax (r := ks) Root.Kind.isMax_cause
  refine ⟨.mono (Root.close.le_closure ks), fun h ↦ ⟨fun hr ↦ ?_, fun hk ↦ h.cause (hc.1 hk),
    fun hk hk' ↦ h.mannerOfCause (hm.1 hk) (hc.1 hk')⟩⟩
  obtain ⟨j, hj, hrj⟩ := Root.mem_close.1 hr
  cases hrj with
  | refl => exact h.change hj
  | result_cause => exact (h.cause hj).entailsChange

theorem Respects.entailsChange (h : M.Respects p Q ks)
    (hr : Root.Kind.result ∈ Root.close ks) : M.EntailsChange p :=
  (respects_close.2 h).change hr

end ArgumentStructure.EventStructure.Model
