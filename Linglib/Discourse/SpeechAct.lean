module

public import Linglib.Discourse.Role
public import Linglib.Syntax.Clause.Basic
public import Mathlib.Order.Max
public import Mathlib.Tactic.DeriveFintype

/-!
# Speech acts

This file defines the illocutionary force of an utterance and the preparatory conditions of a
request for information. The force is the act an utterance performs, the F in F(p): asserting,
asking, commanding, promising or exclaiming. Each sentence type conventionally performs one
force, `Clause.SentenceType.force`, the three interrogatives all asking, and a form used for
another act, a rising declarative that asks or an interrogative that requests, is a mismatch
between that pairing and the act. Lakoff assigns each force the participant with epistemic
authority over its content, the addressee for a question and the speaker otherwise. A speech
act is felicitous only if its preparatory conditions hold, as Searle observes; for a request,
that the addressee is able to do what is requested. The preparatory conditions of a request for
information, in the inventory of Francik and Clark, are the obstacles a speaker may see to
getting the information, partially ordered by specificity.

## Main definitions

* `Discourse.SpeechAct.Force`, `Discourse.SpeechAct.Force.authority`: the forces and Lakoff's
  epistemic authority.
* `Clause.SentenceType.force`: the force a sentence type conventionally performs.
* `Discourse.SpeechAct.PreparatoryCondition`, with its `PartialOrder`.

## References

* [searle-1969]
* [sadock-zwicky-1985]
* [lakoff-1970]
* [francik-clark-1985]
-/

@[expose] public section

namespace Discourse.SpeechAct

/-! ### Illocutionary force -/

/-- The illocutionary force of an utterance is the act it performs, the F in F(p), which its
sentence type conventionally fixes and which form and use may pull apart. -/
inductive Force where
  | declarative
  | interrogative
  | imperative
  | promissive
  | exclamative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The participant Lakoff gives epistemic authority over the content of a force is the
addressee for a question and the speaker otherwise. -/
def Force.authority : Force → Discourse.Role
  | .declarative => .speaker
  | .interrogative => .addressee
  | .imperative => .speaker
  | .promissive => .speaker
  | .exclamative => .speaker

/-! ### Preparatory conditions -/

/-- A preparatory condition of a request for information, an obstacle to compliance. -/
inductive PreparatoryCondition where
  /-- The addressee is able to supply the information. -/
  | ability
  /-- The addressee knows the information. -/
  | knowledge
  /-- The addressee remembers the information. -/
  | memory
  /-- The addressee has noticed the source of the information. -/
  | source
  /-- The addressee is allowed to give the information. -/
  | permission
  /-- The addressee is willing to give the information. -/
  | willingness
  /-- The speaker has not already asked for the information. -/
  | speakerMemory
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace PreparatoryCondition

/-- Satisfying the first condition is a way of satisfying the second: knowing, remembering,
having noticed the source and being allowed to tell are ways of being able to supply the
information, and remembering or having noticed the source are ways of knowing it. -/
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

/-- The force a sentence type conventionally performs, asking for the three interrogatives and
the act of its name for each other type. -/
def Clause.SentenceType.force : Clause.SentenceType → Discourse.SpeechAct.Force
  | .declarative => .declarative
  | .polar | .alternative | .constituent => .interrogative
  | .imperative => .imperative
  | .exclamative => .exclamative
  | .promissive => .promissive

theorem Clause.SentenceType.force_surjective : Function.Surjective Clause.SentenceType.force := by
  decide

theorem Clause.SentenceType.force_eq_interrogative_iff (t : Clause.SentenceType) :
    t.force = .interrogative ↔ t.IsInterrogative := by
  cases t <;> simp [Clause.SentenceType.force, Clause.SentenceType.IsInterrogative]
