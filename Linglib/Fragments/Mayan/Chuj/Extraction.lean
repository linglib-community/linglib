module

public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Mayan.Extraction

/-!
# Chuj Agent Focus and extraction marking

Chuj (Q'anjob'alan Mayan) fronts a focused phrase. A focused transitive subject requires the
Agent Focus form of the verb, which adds *-an* to the stem, as in *ix-il-an* 'saw' with the
woman who saw focused; a focused object leaves the verb in its transitive form, with Set A
cross-referencing the subject, and a fronted intransitive subject or locative leaves the verb as
it is. Alonso-Ovalle and Royer report these facts as background to their study of fronted
*yalnhej* DPs.

## Main declarations

* `Chuj.agentFocus`, `Chuj.voice`: the Agent Focus voice, and the voice of each
  `Mayan.VerbForm`.
* `Chuj.verbForm`: the form of a transitive verb by the argument extracted from it.
* `Chuj.Extraction.realize`: the reflexes the extraction from each site licenses.

## References

* [alonso-ovalle-royer-2024]
-/

@[expose] public section

namespace Chuj

/-- Agent Focus keeps both core terms, as the active does, and is coded by *-an*. -/
def agentFocus : Voice := Voice.agentVoice.marked [.suff "an"]

/-- The voice of each form, the uncoded active for the transitive and Agent Focus for the Agent
Focus form. -/
def voice : Mayan.VerbForm → Voice
  | .transitive => Voice.active
  | .agentFocus => agentFocus

/-- A transitive verb takes the Agent Focus form when its subject is extracted, and the
transitive form otherwise. -/
def verbForm (extracted : Option ArgumentRole) : Mayan.VerbForm :=
  if extracted = some .A then .agentFocus else .transitive

namespace Extraction

/-- The extraction of an argument is marked when it changes the form of the verb, by the marker
of the voice it selects, so that only a transitive subject switches the verb to Agent Focus; a
locative fronts with no change to the verb. The recipient and the other adjuncts are
undescribed. -/
def realize : Mayan.ExtractionSite → Option (Finset (Reflex Mayan.Host))
  | .argument .R => none
  | .argument r => some <|
      if verbForm (some r) = verbForm none then ∅
      else {.morpheme .verb (voice (verbForm (some r))).marker}
  | .adjunct .locative => some ∅
  | .adjunct _ => none

/-- The Agent Focus reflex appears exactly under the extraction of a transitive subject. -/
theorem agentFocus_mem_realize_iff (s : Mayan.ExtractionSite) :
    (∃ m ∈ realize s, Reflex.morpheme .verb agentFocus.marker ∈ m) ↔ s = .argument .A := by
  decide +revert

end Extraction

end Chuj
