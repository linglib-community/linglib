module

public import Linglib.Syntax.Voice.System
public import Linglib.Syntax.Person.Basic

/-!
# Indonesian voice

Indonesian has three constructions for a transitive clause. In the active the verb takes the
prefix *meN-* and the actor is the subject, as in *Mereka sudah menjemput Tomo* 'They have met
Tomo'. In Sneddon's passive type one the verb takes *di-*, the patient is the subject, and the
actor follows the verb, with or without *oleh* 'by', or is not expressed, as in *Tomo sudah
dijemput oleh mereka*. In his passive type two the verb is bare, the patient is the subject and
the actor stands immediately before the verb, after negation and the temporal markers, as in
*Buku ini tidak akan kami baca* 'This book will not be read by us', *aku* and *kamu* usually
appearing as the bound *ku-* and *kau-*. Cole, Hermon and Yanti and Erlewine, Levin and van Urk
call the three the active or subject voice, the passive and the object voice, and with the
subject and object voices [the system is symmetrical](##isSymmetrical_voices) and
[binary](##not_isMultiple_voices).

The actor chooses the passive: type one where it is third person, type two where it is a
pronoun or stands for one, so that [*dia* and *mereka* alone take
both](##takesTypeOne_and_takesTypeTwo_iff) and [every actor takes
one](##takesTypeOne_or_takesTypeTwo).

## Implementation notes

The middle in *ber-* selects no pivot and is the matter of `Verbs.lean`. Passive type one with
a first or second person agent, which Sneddon reports from spontaneous speech, is not admitted,
and the verbs in *ter-*, which take the agent of passive type one in any person, are left out.

## References

* [sneddon-1996]
* [cole-hermon-yanti-2008]
* [erlewine-levin-van-urk-2017]
-/

@[expose] public section

namespace Indonesian

/-- In the active, or subject voice, in *meN-* the actor is the pivot. -/
def subjectVoice : Voice := Voice.agentVoice.marked [.pref "meN"]

/-- In the object voice, Sneddon's passive type two, the verb is bare, the patient is the pivot
and the actor stands before the verb. -/
def objectVoice : Voice := Voice.patientVoice

/-- In the passive in *di-*, Sneddon's passive type one, the patient is the subject and the
actor is at `agent`: not expressed by default, and otherwise after the verb. -/
def diPassive (agent : ArgumentFrame.Position := .implicit) : Voice :=
  (Voice.passive .np agent).marked [.pref "di"]

/-- The three voices. -/
def voices : Voice.System := {subjectVoice, objectVoice, diPassive}

/-- The subject and object voices select the actor and the patient of one construction, so
the system is symmetrical ([erlewine-levin-van-urk-2017]). -/
theorem isSymmetrical_voices : voices.IsSymmetrical := by decide

/-- No voice selects an oblique, an applicative making it an object first
([erlewine-levin-van-urk-2017]), so the system is binary. -/
theorem not_isMultiple_voices : ¬ voices.IsMultiple := by decide

/-! ### The actor and the choice of passive -/

/-- The actor of a transitive clause, by the two questions that choose its passive: its person,
and whether it is a pronoun or a noun ([sneddon-1996] p. 249). -/
inductive Agent where
  /-- A pronoun, as *saya*, *kamu*, *dia* and *mereka*. -/
  | pronoun (person : Person)
  /-- A pronoun substitute, a kinship term or a name standing for the speaker or the
  addressee. -/
  | substitute
  /-- A noun, which is third person. -/
  | noun
  deriving DecidableEq, Repr

namespace Agent

/-- Passive type one is used where the actor is third person, the pronouns *dia* and *mereka*
or a noun ([sneddon-1996] p. 247). -/
def TakesTypeOne (a : Agent) : Prop := a = pronoun .third ∨ a = noun

/-- Passive type two is used where the actor is a pronoun or a pronoun substitute
([sneddon-1996] p. 248). -/
def TakesTypeTwo (a : Agent) : Prop := a ≠ noun

instance : DecidablePred TakesTypeOne := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred TakesTypeTwo := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- Either passive can be used exactly where the actor is a third person pronoun
([sneddon-1996] p. 250). -/
theorem takesTypeOne_and_takesTypeTwo_iff {a : Agent} :
    a.TakesTypeOne ∧ a.TakesTypeTwo ↔ a = pronoun .third := by
  cases a <;> simp [TakesTypeOne, TakesTypeTwo]

/-- Every actor has a passive. -/
theorem takesTypeOne_or_takesTypeTwo (a : Agent) : a.TakesTypeOne ∨ a.TakesTypeTwo := by
  cases a <;> simp [TakesTypeOne, TakesTypeTwo]

end Agent

end Indonesian
