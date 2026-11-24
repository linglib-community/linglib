module

public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Voice.Basic
public import Linglib.Languages.Mayan.Extraction

/-!
# Tsotsil extraction marking

Tsotsil (Tseltalan Mayan) may put the verb in the Agent Focus form in *-on* when a transitive
subject is extracted; Aissen shows the form to be optional and governed by obviation, the form
of a clause whose object outranks its subject. A recipient or benefactive of a transitive verb
is always advanced to direct object by the applicative *-be*, so that it is cross-referenced by
Set B and extracts as the patient does. When an instrument, the object of the preposition *ta*,
is questioned, focused or relativized, the preposition drops and the enclitic *=ˀo* attaches to
the verb; a question with *k'u yu7un* 'why' takes no enclitic.

## Main declarations

* `Tsotsil.agentFocus`: the Agent Focus voice.
* `Tsotsil.Extraction.instrumentEnclitic`: the enclitic *=ˀo*.
* `Tsotsil.Extraction.realize`: the optional Agent Focus reflex of subject extraction, the
  enclitic of instrument extraction, and the unmarked extraction of the other arguments and of
  a reason.

## Implementation notes

The theme beside an applied recipient, a chômeur in Aissen's analysis, and the adjunct classes
other than instruments and reasons are unrecorded. A benefactive of an intransitive verb is an
oblique with the relational noun *-u7un*, so the benefactive cell depends on the verb and is
unrecorded too.

## References

* [aissen-1987]
* [aissen-1999a]
* [polian-2017b]
-/

@[expose] public section

namespace Tsotsil

/-- Agent Focus keeps both core terms, as the active does, and is coded by *-on*. -/
def agentFocus : Voice := Voice.agentVoice.marked [.suff "on"]

namespace Extraction

/-- The enclitic *=ˀo*, which replaces the preposition *ta* of an extracted instrument. -/
def instrumentEnclitic : Morphology.Morph := .encl "ˀo"

/-- The extraction of a transitive subject may switch the verb to Agent Focus, used when the
object outranks the subject in obviation ([aissen-1999a]); the extraction of an instrument puts
*=ˀo* on the verb ([aissen-1987] p. 14, [polian-2017b] p. 632); the intransitive subject, the
patient, the recipient, which the applicative makes a direct object ([aissen-1987] ch. 7), and a
reason ([aissen-1987] p. 14) extract unmarked. -/
def realize : Mayan.ExtractionSite → Option (Finset (Reflex Mayan.Host))
  | .argument .A => some {.morpheme .verb agentFocus.marker}
  | .argument .S | .argument .P | .argument .R | .adjunct .reason => some ∅
  | .adjunct .instrument => some {.morpheme .verbalComplex [instrumentEnclitic]}
  | _ => none

end Extraction

end Tsotsil
