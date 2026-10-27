module

public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Role
public import Linglib.Syntax.Clause.Basic
public import Mathlib.Order.Max
public import Mathlib.Tactic.DeriveFintype

/-!
# Speech acts

The *illocutionary force* of an utterance is the act it performs, the $F$ in $F(p)$: an assertion,
a question, a directive, a promise or an exclamation. Each sentence type
[conventionally performs one force](##Clause.SentenceType.force), every interrogative a question,
and a form used for another act, a rising declarative that asks or an interrogative that
requests, departs from that pairing.

The *epistemic authority* of an act is the participant whose commitment to its content the act
projects. In Krifka's commitment spaces an assertion adds the speaker's commitment to its content
and a polar question proposes the addressee's commitment to it or to its negation, so the
authority is [the speaker of an assertion and the addressee of a
question](##Discourse.SpeechAct.Force.authority_eq_some_iff): the interrogative flip is the
difference between the two updates.

A request is felicitous only if its *preparatory conditions* hold, first among them that the
addressee is able to do what is requested, and asking whether the addressee is able is a way of
making the request indirectly. A question is a request for information, and the conditions on giving
information are [ordered by specificity](##Discourse.SpeechAct.PreparatoryCondition.le), knowing
it being a way of being able to give it.

## Main definitions

* `Discourse.SpeechAct.Force`: the illocutionary forces.
* `Discourse.SpeechAct.Force.authority`: the epistemic authority of an assertion or a question.
* `Discourse.SpeechAct.Force.commitmentUpdate`: an assertion or a question as an update of a
  commitment space.
* `Clause.SentenceType.force`: the force a sentence type conventionally performs.
* `Discourse.SpeechAct.PreparatoryCondition`: the preparatory conditions of a request, with their
  `PartialOrder`.

## Implementation notes

* The authority is partial. Coppock and Wechsler assign it for declaratives and polar
  interrogatives, and Theiler's source of information is the same participant for assertions and
  questions. For imperatives the sources diverge: Speas and Tenny's seat of knowledge, which
  Coppock and Wechsler equate with the authority, is the hearer, who is to realize the content,
  while Searle's command requires the speaker's authority over the hearer, a deontic notion.
* The authority is not definable over the Table of Farkas and Bruce, where a polar question
  raises an issue and commits no one (`Commitment.Table.polarQuestion`); Coppock and Wechsler,
  who work over the Table, take it as a parameter of the context. It is definable over Krifka's
  commitment spaces, whose questions propose the addressee's commitment.
* Searle counts the addressee's wanting to do what is requested among the reasons for doing it,
  not among the preparatory conditions; Francik and Clark count willingness among the
  preconditions of a request.

## References

* [searle-1969]
* [searle-1979]
* [sadock-zwicky-1985]
* [krifka-2015]
* [speas-tenny-2003]
* [coppock-wechsler-2018]
* [theiler-2021]
* [francik-clark-1985]
-/

@[expose] public section

namespace Discourse.SpeechAct

/-! ### Illocutionary force -/

/-- The illocutionary force of an utterance is the act it performs, the $F$ in $F(p)$, which its
sentence type conventionally fixes and which form and use may pull apart. -/
inductive Force where
  /-- Putting the content forward as true. -/
  | assertion
  /-- Asking the addressee for information. -/
  | question
  /-- Trying to get the addressee to act, as a command or a request does. -/
  | directive
  /-- Committing the speaker to act. -/
  | promise
  /-- Expressing the speaker's attitude to the content. -/
  | exclamation
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Force

/-- The epistemic authority of an act is the participant whose commitment to its content the act
projects: the speaker of an assertion and the addressee of a question. The other acts have
none. -/
def authority : Force → Option Discourse.Role
  | assertion => some .speaker
  | question => some .addressee
  | directive | promise | exclamation => none

@[simp] theorem authority_assertion : assertion.authority = some .speaker := rfl

@[simp] theorem authority_question : question.authority = some .addressee := rfl

/-! ### Authority from projected commitments -/

section Commitment

open Commitment

variable {W : Type*} (C : Commitment.Space (Set (Set W))) (O : Discourse.Role → SetRel W W)
  (φ : Set W)

/-- An act of force `f` with content `φ` as an update of a commitment space, after Krifka: an
assertion adds the speaker's commitment to `φ`, and a question proposes the addressee's
commitment to `φ` or to `¬φ`. Commitment Space Semantics gives the other forces no such
update. -/
def commitmentUpdate : Force → Option (Commitment.Space (Set (Set W)))
  | assertion => some (C.assert O .speaker φ)
  | question => some (C.bipolarQuestion O .addressee φ)
  | directive | promise | exclamation => none

variable {C O φ}

/-- An act projects the commitment of its authority. -/
theorem projectsCommitment_of_authority_eq_some {f : Force} {r : Discourse.Role}
    (hr : f.authority = some r) {D : Commitment.Space (Set (Set W))}
    (hD : D ∈ f.commitmentUpdate C O φ) : C.ProjectsCommitment O r φ D := by
  cases f <;> cases hr <;> cases hD
  exacts [C.projectsCommitment_assert O .speaker φ,
    C.projectsCommitment_bipolarQuestion O .addressee φ]

/-- Coppock and Wechsler's epistemic authority is the participant whose commitment the act
projects: when the participants' commitments to `φ` and to `¬φ` are four distinct propositions,
the authority of an assertion or a question is exactly the participant whose commitment its
update of the space of all states projects. -/
theorem authority_eq_some_iff
    (hO : Function.Injective fun x : Discourse.Role × Bool ↦
      committed O x.1 (bif x.2 then φ else φᶜ))
    {f : Force} {D : Commitment.Space (Set (Set W))}
    (hD : D ∈ f.commitmentUpdate (.Ici ∅) O φ) (r : Discourse.Role) :
    f.authority = some r ↔ (Commitment.Space.Ici ∅).ProjectsCommitment O r φ D := by
  refine ⟨fun hr ↦ projectsCommitment_of_authority_eq_some hr hD, fun h ↦ ?_⟩
  cases f <;> cases hD <;> cases r
  · rfl
  · rcases Commitment.Space.projectsCommitment_Ici_assert_iff.1 h with e | e
    · cases hO (a₁ := (.addressee, true)) (a₂ := (.speaker, true)) e
    · cases hO (a₁ := (.addressee, false)) (a₂ := (.speaker, true)) e
  · rcases (Commitment.Space.projectsCommitment_Ici_bipolarQuestion_iff.1 h).1 with e | e
    · cases hO (a₁ := (.speaker, true)) (a₂ := (.addressee, true)) e
    · cases hO (a₁ := (.speaker, false)) (a₂ := (.addressee, true)) e
  · rfl

/-- In the canonical model, where each participant's commitments leave open a set of facts, the
participants' commitments to a fact and to its negation are four distinct propositions. -/
private theorem injective_committed_index : Function.Injective fun x : Discourse.Role × Bool ↦
    committed (Index.access (F := Bool)) x.1
      (bif x.2 then Index.fact ⁻¹' {true} else (Index.fact ⁻¹' {true})ᶜ) := by
  have hX (b : Bool) : (bif b then Index.fact ⁻¹' {true} else (Index.fact ⁻¹' {true})ᶜ :
      Set (Index Discourse.Role Bool)) = Index.fact ⁻¹' {b} := by
    cases b <;> ext <;> simp
  rintro ⟨r, b⟩ ⟨r', b'⟩ h
  simp only [hX, Index.committed_access_preimage] at h
  let w : Index Discourse.Role Bool :=
    ⟨b, fun q ↦ if q = r then {b} else Set.univ, fun q ↦ by split_ifs <;> simp⟩
  have hw : w.commitmentSet r' ⊆ {b'} := (Set.ext_iff.1 h w).1 (by simp [w])
  by_cases hr : r' = r
  · subst hr
    obtain rfl : b = b' := by simpa [w] using hw
    rfl
  · exact absurd (hw (show (!b') ∈ w.commitmentSet r' by simp [w, hr])) (by simp)

/-- In the canonical model a question does not project the speaker's commitment. -/
example : ¬ (Commitment.Space.Ici ∅).ProjectsCommitment (Index.access (F := Bool)) .speaker
    (Index.fact ⁻¹' {true}) ((Commitment.Space.Ici ∅).bipolarQuestion
      (Index.access (κ := Discourse.Role)) .addressee (Index.fact ⁻¹' {true})) :=
  fun h ↦ absurd ((authority_eq_some_iff injective_committed_index (f := .question) rfl _).2 h)
    (by simp)

end Commitment

end Force

/-! ### Preparatory conditions -/

/-- A preparatory condition of a request is one that must hold for the addressee to comply: that
the addressee is able and willing to do what is requested, and, when what is requested is
information, the ways of being able to give it and the speaker's not having asked for it
already. Searle's preparatory condition of a request is the addressee's ability, and on his
first generalization about indirect speech acts asking whether it holds is a way of making the
request. -/
inductive PreparatoryCondition where
  /-- The addressee is able to do what is requested. -/
  | ability
  /-- The addressee knows the information. -/
  | knowledge
  /-- The addressee remembers the information. -/
  | memory
  /-- The addressee has noticed the source of the information. -/
  | source
  /-- The addressee is allowed to do what is requested. -/
  | permission
  /-- The addressee is willing to do what is requested. -/
  | willingness
  /-- The speaker has not already asked for the information. -/
  | speakerMemory
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace PreparatoryCondition

/-- Satisfying the first condition is a way of satisfying the second: knowing, remembering,
having noticed the source and being allowed to tell are ways of being able to give the
information, and remembering or having noticed the source are ways of knowing it. Willingness
and the speaker's memory stand apart, so the order has neither a top nor a bottom. Being allowed
falls under being able as in Francik and Clark's gloss of an addressee unable to tell, although
their scenarios on it were written as borderline between ability and willingness. -/
protected def le : PreparatoryCondition → PreparatoryCondition → Prop
  | .knowledge, .ability | .memory, .ability | .source, .ability | .permission, .ability
  | .memory, .knowledge | .source, .knowledge => True
  | c, d => c = d

instance : DecidableRel PreparatoryCondition.le := fun c d ↦ by
  cases c <;> cases d <;> unfold PreparatoryCondition.le <;> infer_instance

instance : LE PreparatoryCondition := ⟨PreparatoryCondition.le⟩

instance : DecidableLE PreparatoryCondition :=
  inferInstanceAs (DecidableRel PreparatoryCondition.le)

instance : PartialOrder PreparatoryCondition where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : NoTopOrder PreparatoryCondition := ⟨by decide⟩

instance : NoBotOrder PreparatoryCondition := ⟨by decide⟩

end PreparatoryCondition

end Discourse.SpeechAct

/-! ### The conventional force of a sentence type -/

namespace Clause.SentenceType

open Discourse.SpeechAct (Force)

/-- The force a sentence type conventionally performs: a question for each of the three
interrogatives, and for each other type the act it is named for. -/
def force : SentenceType → Force
  | declarative => .assertion
  | polar | alternative | constituent => .question
  | imperative => .directive
  | exclamative => .exclamation
  | promissive => .promise

theorem force_surjective : Function.Surjective force := by decide

theorem force_eq_question_iff {t : SentenceType} : t.force = .question ↔ t.IsInterrogative := by
  cases t <;> simp [force, IsInterrogative]

end Clause.SentenceType
