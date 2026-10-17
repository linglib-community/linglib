module

public import Linglib.Semantics.Evidential.Defs
public import Linglib.Semantics.Aspect.Defs

/-!
# Kashaya evidentiality

Kashaya (Pomoan, northern California) marks the source of the speaker's information with a
paradigm of verbal suffixes, which Oswalt lays out in his Table 1 and which Aikhenvald sets
beside the five-choice systems as a complex system with further terms.
The rows of the table are the evidentials, top down in the order of Oswalt's hierarchy of
preference; its columns are the modes of speech. A spontaneous remark, prompted by the event
itself, makes the finest distinctions: the performative pair *-ŵela* ~ *-mela*, the speaker
performing or having just performed the act, so that the subject is first person; the
factual-visual pair *-ŵă* ~ *-yă*, the speaker seeing or having seen it, the imperfective
factual also stating general truths and common knowledge; the auditory *-V̂nnă*, the sound of
the action heard but not seen; inferential I *-qă*, inference from evidence found apart from the
event; and the quotative *-do*, information learned from someone else. The performative and the
factual-visual are complementary pairs selected by the aspect of the stem, the imperfective
member for imperfective stems and the perfective for perfective ones, an aspectless stem taking
either. A response to another's words adds the suffix *-m* and drops the performative, the
factual-visual pair taking its place. The narrative construction, with the evidential on the
assertive enclitic and the main verb in the absolutive, collapses all direct evidence to the
personal experience *-yowă* against the quotative, and the archaic remote past *-miyă* marks
personal experience in an irretrievable past. Inferential II *-bi-* is never verb-final: it
precedes a subordinating suffix, the absolutive or another evidential, so it stands outside the
mutually exclusive paradigm. WALS codes the language as having direct and indirect evidentials
(Feature 77A).

## Implementation notes

The forms are Oswalt's morphophonemic suffixes in Aikhenvald's typography, *ŵ* an initial that
surfaces only after a vowel, *V̂* a vowel determined by the preceding consonant and *ă* a final
vowel that is zero before a word boundary. The performative covers none of Aikhenvald's six
parameters: its source, the speaker's own act, lies outside them. The general truths the
factual states are general knowledge cast in the visual, an extension of its coverage rather
than a parameter of its own. The six parameters cannot split hearing from the other senses, so
the auditory carries the whole non-visual sensory parameter although Oswalt notes that smell
and touch fall by default to inferential I.

## References

* [oswalt-1986]
* [aikhenvald-2004]
* [de-haan-2013]
-/

@[expose] public section

namespace Kashaya.Evidentiality

open Evidential Aspect

/-- The modes of speech, the columns of Oswalt's Table 1: the spontaneous remark, the response
marked by *-m*, the narrative construction and the remote past. -/
inductive Mode
  | spontaneous
  | responsive
  | narrative
  | remote
  deriving DecidableEq, Repr

/-- The performative pair *-ŵela* ~ *-mela*: the speaker performs or has just performed the act.
Its source lies outside the six parameters, so it covers none. -/
def performative : Perfectivity → Evidential
  | .imperfective => { morphs := [.suff "ŵela"], covers := ∅ }
  | .perfective => { morphs := [.suff "mela"], covers := ∅ }

/-- The factual-visual pair: the speaker sees or saw the event. The imperfective factual *-ŵă*
also states general truths and common knowledge, general knowledge cast in the visual; the
perfective visual *-yă* does not. -/
def factualVisual : Perfectivity → Evidential
  | .imperfective => { morphs := [.suff "ŵă"], covers := {.visual} }
  | .perfective => { morphs := [.suff "yă"], covers := {.visual} }

/-- The auditory *-V̂nnă*: the speaker heard the sound of the action but did not see it. -/
def auditory : Evidential :=
  { morphs := [.suff "V̂nnă"], covers := {.sensory} }

/-- Inferential I *-qă*: inference from circumstances or evidence found apart, in space or time,
from the event. -/
def inferential : Evidential :=
  { morphs := [.suff "qă"], covers := {.inference} }

/-- The quotative *-do*: information learned from someone else. -/
def quotative : Evidential :=
  { morphs := [.suff "do"], covers := {.hearsay, .quotative} }

/-- Inferential II *-bi-*, which must be followed by another suffix: a subordinator, the
absolutive in *-biw* 'it turned out', the quotative or inferential I. -/
def inferentialII : Evidential :=
  { morphs := [.suff "bi"], covers := {.inference} }

/-- The personal experience *-yowă* of the narrative construction, the factual on an element
*-yo-*, which replaces every evidential of direct evidence. -/
def personalExperience : Evidential :=
  { morphs := [.suff "yowă"], covers := {.visual, .sensory, .inference} }

/-- The archaic remote past *-miyă*, the visual on an element *-mi-*: personal experience in an
irretrievable past. -/
def remotePast : Evidential :=
  { morphs := [.suff "miyă"], covers := {.visual, .sensory, .inference} }

/-- The paradigm of a mode for stems of an aspect is a column of Table 1 read top down, in the
order of Oswalt's hierarchy. -/
def paradigm : Mode → Perfectivity → List Evidential
  | .spontaneous, a => [performative a, factualVisual a, auditory, inferential, quotative]
  | .responsive, a => [factualVisual a, auditory, inferential, quotative]
  | .narrative, _ => [personalExperience, quotative]
  | .remote, _ => [remotePast, quotative]

end Kashaya.Evidentiality
