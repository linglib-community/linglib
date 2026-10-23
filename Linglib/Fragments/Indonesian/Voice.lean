module

public import Linglib.Syntax.Voice.System
public import Linglib.Syntax.Person.Basic

/-!
# Indonesian voice

Indonesian has three voices projecting transitive clauses. In the subject voice the verb takes
the prefix *meN-*, whose nasal assimilates to the stem, and the agent is the subject, as in
*Tono membeli buku* 'Tono bought a book'. In the object voice the verb is bare, the patient is
the subject and the agent stands immediately before the verb, after negation and the
auxiliaries, as in *Topi ini sudah saya beli* 'I have bought this hat'; the agent is
obligatory and pronominal, *aku* and *kamu* appearing as the bound *ku-* and *kau-*. In the
*di-* voice the patient is the subject and the agent follows the verb, bare or with *oleh*
'by', and may be omitted, as in *Kue ini dimakan (oleh) Arna* 'This cake was eaten by Arna';
its agent is third person, *dia*, *mereka* or a noun, so that the third-person pronouns alone
take both patient-subject voices. The middle *ber-* selects no pivot and is the matter of
`Verbs.lean` and `Studies/BeaversUdayana2022.lean`. Sneddon, Cole, Hermon and Yanti, and
Erlewine, Levin and van Urk describe the three voices, which Erlewine, Levin and van Urk take as
a subject and an object voice beside a passive. Creissels finds *di-* ambiguous between a patient voice, whose bare postverbal
agent remains a core term and which then forms a binary symmetrical system with *meN-*, and a
passive whose agent is demoted to the *oleh*-phrase, *meN-* then marking transitivity.

## Main definitions

* `Indonesian.subjectVoice`, `objectVoice`, `di` — the three voices, *di-* under a reading
* `Indonesian.DiReading` — Creissels's two readings of *di-*
* `Indonesian.voices` — the inventory under a reading
* `Indonesian.Agent`, `objectVoiceAgents`, `diAgents` — the forms of the agent each
  patient-subject voice takes

## Main results

* `Indonesian.isSymmetrical_voices`, `not_isMultiple_voices` — the subject and object voices
  form a binary symmetrical system on either reading of *di-*
* `Indonesian.isSymmetrical_pair_iff` — *meN-* and *di-* form one exactly under the
  patient-voice reading
* `Indonesian.objectVoiceAgents_inter_diAgents` — the third-person pronouns alone take
  both patient-subject voices
* `Indonesian.objectVoiceAgents_union_diAgents` — every agent has a patient-subject voice

## References

* [cole-hermon-yanti-2008]
* [creissels-2024]
* [erlewine-levin-van-urk-2017]
* [sneddon-1996]
-/

@[expose] public section

namespace Indonesian

/-- In the subject voice *meN-* the agent is the pivot. -/
def subjectVoice : Voice := Voice.agentVoice.marked [.pref "meN"]

/-- In the object voice, the bare verb, the patient is the pivot and the agent a preverbal
pronoun. -/
def objectVoice : Voice := Voice.patientVoice

/-- *di-* reads as a patient voice whose bare postverbal agent remains a core term, or as a
passive whose agent is demoted to the *oleh*-phrase ([creissels-2024]). -/
inductive DiReading where
  | patientVoice
  | passive
  deriving DecidableEq, Repr, Fintype

/-- Under a reading, the *di-* voice is the patient voice or the passive marked by *di-*. -/
def di : DiReading → Voice
  | .patientVoice => Voice.patientVoice.marked [.pref "di"]
  | .passive => Voice.passive.marked [.pref "di"]

/-- The three voices under a reading of *di-*. -/
def voices (r : DiReading) : Voice.System := {subjectVoice, objectVoice, di r}

/-- *meN-* and *di-* form a binary symmetrical system exactly when *di-* is read as a patient
voice ([creissels-2024]). -/
theorem isSymmetrical_pair_iff (r : DiReading) :
    ({subjectVoice, di r} : Voice.System).IsSymmetrical ↔ r = .patientVoice := by
  cases r <;> decide

/-- The subject and object voices select the agent and the patient whatever *di-* is, so
Indonesian has a symmetrical system on either reading ([erlewine-levin-van-urk-2017]). -/
theorem isSymmetrical_voices (r : DiReading) : (voices r).IsSymmetrical :=
  Voice.System.IsSymmetrical.mono (S := {subjectVoice, objectVoice}) (by decide) <|
    Finset.insert_subset_insert _ <| Finset.singleton_subset_iff.2 <| Finset.mem_insert_self _ _

/-- No voice selects an oblique, an applicative making it an object first
([erlewine-levin-van-urk-2017]), so the system is binary. -/
theorem not_isMultiple_voices (r : DiReading) : ¬ (voices r).IsMultiple := by
  cases r <;> decide

/-! ### The agent of the patient-subject voices -/

/-- The agent of a transitive clause is a pronoun of a person, a noun, or absent. -/
inductive Agent where
  | pronoun (person : Person)
  | noun
  | absent
  deriving DecidableEq, Repr, Fintype

/-- The agent is a pronoun. -/
def Agent.IsPronoun : Agent → Prop
  | .pronoun _ => True
  | _ => False

instance : DecidablePred Agent.IsPronoun := fun a ↦ by
  cases a <;> unfold Agent.IsPronoun <;> infer_instance

/-- The object voice takes a pronoun of any person as its agent, obligatorily. -/
def objectVoiceAgents : Finset Agent := Finset.univ.filter Agent.IsPronoun

/-- The *di-* voice takes a third-person pronoun, a noun, or no agent. -/
def diAgents : Finset Agent := {.pronoun .third, .noun, .absent}

/-- The third-person pronouns *dia* and *mereka* alone take both patient-subject voices
([sneddon-1996]). -/
theorem objectVoiceAgents_inter_diAgents :
    objectVoiceAgents ∩ diAgents = {.pronoun .third} := by
  decide

/-- Every agent, expressed or not, has a patient-subject voice. -/
theorem objectVoiceAgents_union_diAgents : objectVoiceAgents ∪ diAgents = Finset.univ := by
  decide

end Indonesian
