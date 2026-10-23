module

public import Linglib.Fragments.Mayan.Kaqchikel.Extraction

/-!
# Kaqchikel focus

In Patzún Kaqchikel a focused argument fronts to the position immediately before the verb and
is marked by the particle *ja*; a focused transitive subject also switches the verb to Agent
Focus, which an intransitive verb lacks, so the subjects split by transitivity. Erlewine counts
focus as one of four constructions that trigger Agent Focus, with wh-questions, relative clauses
and argument existentials, and a subject-initial clause without *ja* is a topic, not a focus.
Across Mayan, Aissen finds, information focus stays in situ and unmarked except on a transitive
subject, which in the Agent Focus languages must front.

## Main declarations

* `Kaqchikel.focusRealize`: the reflexes of focusing an argument, those of its extraction with
  the fronting and *ja*.
* `Kaqchikel.agentFocus_mem_focusRealize_iff`: Agent Focus marks the focus of a transitive
  subject unless both arguments are speech-act participants.

## Implementation notes

`focusRealize` covers the fronted construction only; Kaqchikel in-situ focus is not in these
sources, so no claim that every focus is overtly marked is made. A focused recipient, a phrase
with a relational noun, also brings *wi*, as its extraction does.

## References

* [aissen-2017]
* [erlewine-2016]
-/

@[expose] public section

namespace Kaqchikel

/-- The focus particle *ja*. -/
def ja : Morphology.Morph := .free "ja"

/-- A focused argument fronts, never string-vacuously since the base order is VOS, and hosts
*ja*, on top of the reflexes its extraction licenses ([erlewine-2016]). -/
def focusRealize (c : Mayan.VerbClass) (agent patient : Person) (r : ArgumentRole) :
    Finset (Reflex Mayan.Host) :=
  Extraction.realize c agent patient (.argument r) ∪
    {.displacement .phrase, .morpheme .phrase [ja]}

theorem agentFocus_mem_focusRealize_iff (c : Mayan.VerbClass) (agent patient : Person)
    (r : ArgumentRole) :
    Reflex.morpheme .verb (agentFocus c).marker ∈ focusRealize c agent patient r ↔
      r = .A ∧ ¬ (agent.IsSAP ∧ patient.IsSAP) := by
  simp [focusRealize, Extraction.agentFocus_mem_realize_iff]

end Kaqchikel
