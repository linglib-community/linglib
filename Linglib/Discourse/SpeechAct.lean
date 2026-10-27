module

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
requests, departs from that pairing. The *epistemic authority* of an act is the participant whose
commitment to its content the act projects, [the speaker of an assertion and the addressee of a
question](##Discourse.SpeechAct.Force.authority). A request is felicitous only if its
*preparatory conditions* hold, first among them that the addressee is able to do what is
requested; a question is a request for information, and the conditions on giving information are
[ordered by specificity](##Discourse.SpeechAct.PreparatoryCondition.le), knowing it being a way
of being able to give it.

## Main definitions

* `Discourse.SpeechAct.Force`: the illocutionary forces.
* `Discourse.SpeechAct.Force.authority`: the epistemic authority of an assertion or a question.
* `Clause.SentenceType.force`: the force a sentence type conventionally performs.
* `Discourse.SpeechAct.PreparatoryCondition`: the preparatory conditions of a request, with their
  `PartialOrder`.

## Implementation notes

The authority is partial. Coppock and Wechsler assign it for declaratives and polar
interrogatives, and Theiler's source of information is the same participant for assertions and
questions. For imperatives the sources diverge: Speas and Tenny's seat of knowledge, which
Coppock and Wechsler equate with the authority, is the hearer, who is to realize the content,
while Searle's command requires the speaker's authority over the hearer, a deontic notion.

## References

* [searle-1969]
* [sadock-zwicky-1985]
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

end Force

/-! ### Preparatory conditions -/

/-- A preparatory condition of a request is one that must hold for the addressee to comply: that
the addressee is able and willing to do what is requested, and, when what is requested is
information, the ways of being able to give it and the speaker's not having asked for it
already. -/
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
