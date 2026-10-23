module

public import Linglib.Syntax.Voice.Basic

/-!
# Mam voice

Mam (Mamean Mayan) has an antipassive and several passives, described in England's sketch and,
for San Juan Atitán Mam, in Scott's grammar. The antipassive suffix *-n*, *-an* after a
consonant, makes the subject the sole argument marked on the verb, by Set B, and demotes the
object to a phrase with a relational noun; it serves for an unmentioned patient, for an
incorporated object and for the extraction of a transitive subject, Mam having no agent-focus
form of its own (`Extraction.lean`). Of the passives, the general syntactic ones are *-Vt*,
*-et* in San Juan Atitán, and a null one, both making the patient the sole argument marked on
the verb, the agent optional in a phrase with the agentive relational noun *-u'n*; the lexical
passive *-j* adds that the agent lost control of the action. Mam has no applicative and no
productive causative.

## Implementation notes

The null passive has the empty marker and so is uncoded in Creissels's sense, an alternation
with no verbal coding, as his reading of the Bambara passive is; the frame pair records what
tells it from the active, an intransitive derived construction with the agent maintained, and
the Set B marking follows from that transitivity. That Ø fills the paradigm slot of *-Vt* and
*-j* is the Mayanist analysis of the paradigm and is left to the studies.

## Main definitions

* `Mam.active`, `antipassive`, `passive`, `nullPassive`, `lexicalPassive` — the voices
* `Mam.voices` — the inventory

## Main results

* `Mam.not_isTransitive_of_ne_active` — every voice but the active derives an intransitive
  construction

## References

* [england-2017]
* [scott-2023]
-/

@[expose] public section

namespace Mam

/-- The active, the transitive construction. -/
def active : Voice := Voice.active

/-- The antipassive *-n*, the object demoted to a relational-noun phrase. -/
def antipassive : Voice := Voice.antipassive.marked [.suff "n"]

/-- The general passive *-Vt*, the agent optional in an *-u'n*-phrase. -/
def passive : Voice := Voice.passive.marked [.suff "Vt"]

/-- The general passive with no suffix, told from the active by its intransitive
inflection. -/
def nullPassive : Voice := Voice.passive

/-- The lexical passive *-j*, the agent having lost control of the action. -/
def lexicalPassive : Voice := Voice.passive.marked [.suff "j"]

/-- The active, the antipassive and the three passives. -/
def voices : Finset Voice := {active, antipassive, passive, nullPassive, lexicalPassive}

theorem not_isTransitive_of_ne_active : ∀ v ∈ voices, v ≠ active → ¬ v.derived.IsTransitive := by
  decide

end Mam
