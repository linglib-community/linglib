module

public import Linglib.Syntax.Voice.System

/-!
# Toba Batak voice

Toba Batak (Austronesian; Lake Toba, Sumatra) is predicate-initial and has two voices, the
actor voice in *mang-*, with its phonologically conditioned variants, and the object voice in
*di-*, as in *Manjaha buku si Poltak* and *Dijaha si Poltak buku*, both 'Poltak read the
book'. Each voice makes one argument the pivot, the clause-peripheral subject, and neither
demotes the other core argument: the agent of the object voice remains a core term, so the
system is symmetric like those of the neighbouring Malayic languages, though the Austronesianist
literature calls the voices active and passive. Among the core arguments only the pivot can be
extracted, while obliques extract under either voice; the restriction is the subject-only gap
relativizer of `Relativization.lean`, and the voice inventory says which argument the pivot is.
The voice prefix surfaces in every clause, so it is not a reflex of extraction, and neither
voice is morphologically basic. Analyses of the extraction restriction, and the examples that
support them, live in the studies that propose them.

## Main definitions

* `TobaBatak.actorVoice`, `TobaBatak.objectVoice` — the two voices with their prefixes
* `TobaBatak.voices` — the inventory

## Main results

* `TobaBatak.isSymmetrical_voices`, `not_isMultiple_voices`, `isEquipollent_voices` — a binary
  symmetrical system with equipollent marking

## References

* [cole-hermon-2008]
* [erlewine-2018]
-/

@[expose] public section

namespace TobaBatak

/-- In the actor voice *mang-* the agent is the pivot. -/
def actorVoice : Voice := Voice.agentVoice.marked [.pref "mang"]

/-- In the object voice *di-* the patient is the pivot and the agent is still a core term. -/
def objectVoice : Voice := Voice.patientVoice.marked [.pref "di"]

/-- The two voices. -/
def voices : Voice.System := {actorVoice, objectVoice}

theorem isSymmetrical_voices : voices.IsSymmetrical := by decide

theorem not_isMultiple_voices : ¬ voices.IsMultiple := by decide

theorem isEquipollent_voices : voices.IsEquipollent := by decide

end TobaBatak
