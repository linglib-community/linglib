module

public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Voice.Basic
public import Linglib.Syntax.Person.Basic
public import Linglib.Fragments.Mayan.Extraction
public import Linglib.Fragments.Mayan.Verb

/-!
# Kaqchikel extraction marking

Kaqchikel (K'ichean Mayan), in the Patzún variety Erlewine describes, marks the Ā-extraction of
a transitive subject with Agent Focus, a voice that keeps both arguments but drops Set A and adds
a suffix: *-n* on a stem ending in a vowel or in *-j*, which it replaces, and *-ö* otherwise.
Object and intransitive-subject extraction never trigger it, long-distance subject extraction
triggers it on the embedded verb alone, material between the extracted subject and the verb
obviates it, and when both arguments are first or second person the full transitive appears
instead. In the elicited production of Heaton, Deen and O'Grady, subject relative clauses mostly
keep the transitive verb with Set A, while the subject questions of speakers over thirty take
Agent Focus or the antipassive. Extraction of a recipient, a phrase with a relational noun, or of
a locative, instrument or benefactive phrase may add the fronting particle *wi* to the verbal
complex, optionally in this variety and with benefactives, which some varieties exclude; reasons
and temporals never license it, and manners and purposes are unattested with it.

## Main declarations

* `Kaqchikel.agentFocus`: the Agent Focus voice of each verb class.
* `Kaqchikel.Extraction.realize`: the reflexes extraction from each `Mayan.ExtractionSite`
  licenses on a verb of each class whose arguments have the given persons.
* `Kaqchikel.Extraction.agentFocus_mem_realize_iff`: Agent Focus marks transitive-subject
  extraction unless both arguments are speech-act participants.

## Implementation notes

`realize` records the Patzún judgments: extraction to the position immediately above the clause,
nothing intervening. The obviation by intervening material is the competition of
`Studies/Erlewine2016.lean`.

## References

* [elkins-torrence-brown-2026]
* [erlewine-2016]
* [heaton-deen-ogrady-2016]
* [mendes-ranero-2021]
-/

@[expose] public section

namespace Kaqchikel

/-- Agent Focus keeps both core terms, as the active does, and is coded by *-n* on a derived
verb, whose stem ends in a vowel or in the *-j* the suffix replaces, and by *-ö* on a radical one
([erlewine-2016] fn. 24). -/
def agentFocus : Mayan.VerbClass → Voice
  | .derived => Voice.agentVoice.marked [.suff "n"]
  | .radical => Voice.agentVoice.marked [.suff "ö"]

namespace Extraction

/-- The fronting particle *wi*. -/
def wi : Morphology.Morph := .free "wi"

/-- Extraction of a transitive subject switches the verb to Agent Focus unless both arguments are
speech-act participants ([erlewine-2016]); extraction of a recipient or of a locative,
instrument or benefactive phrase licenses *wi* on the verbal complex ([mendes-ranero-2021]);
nothing else is marked. -/
def realize (c : Mayan.VerbClass) (agent patient : Person) :
    Mayan.ExtractionSite → Finset (Reflex Mayan.Host)
  | .argument .A =>
      if agent.IsSAP ∧ patient.IsSAP then ∅ else {.morpheme .verb (agentFocus c).marker}
  | .argument .R | .adjunct .instrument | .adjunct .benefactive | .adjunct .locative =>
      {.morpheme .verbalComplex [wi]}
  | _ => ∅

/-- Agent Focus marks the extraction of a transitive subject unless both arguments are speech-act
participants, and nothing else. -/
theorem agentFocus_mem_realize_iff (c : Mayan.VerbClass) (agent patient : Person)
    (s : Mayan.ExtractionSite) :
    Reflex.morpheme .verb (agentFocus c).marker ∈ realize c agent patient s ↔
      s = .argument .A ∧ ¬ (agent.IsSAP ∧ patient.IsSAP) := by
  rcases s with (_ | _ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _) <;>
    by_cases h : agent.IsSAP ∧ patient.IsSAP <;> cases c <;> simp [realize, agentFocus, h]

end Extraction

end Kaqchikel
