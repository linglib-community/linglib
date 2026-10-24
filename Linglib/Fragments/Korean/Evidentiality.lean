module

public import Linglib.Semantics.Tense.Evidential

/-!
# Korean evidentiality

Korean marks information source with optional inflectional suffixes in three subclasses,
perceptual, quotative and reported, and inferential. The members of a subclass are paradigmatic
alternatives, while the subclasses fill distinct slots of the predicate, in the order
inferential, perceptual, reported, and can co-occur, so the terms form no single paradigm. The
perceptual *-te* and *-ney* cover the same sources, the senses and inference from concrete
evidence, and differ in when the evidence was perceived, before speech or at it, which they
carry as the cell of the acquisition relative to speech. The conjecture *-keyss*, the
suppositive *-ci*, the prediction *-ul-kes-i* and the presumption *-ulkel*, which some count as
evidentials, are taken as modal, and the inventory records none of them.

Aikhenvald took the retrospective *-te*, which validates past perception, observation or
experience, as not a primarily evidential form, and the constructions for talking about other
people's feelings as evidentiality strategies. WALS codes the language as having indirect
evidentials only; no term of the inventory covers the senses alone. Cumming's tense-evidential
paradigm, after Lee, composes the acquisition cells of *-te* and *-ney* with tense in
`Studies/Cumming2026.lean`.

## Implementation notes

Forms are in the Yale romanization. A form is cited by one of its variants: *-tay* stands for
*-ta(y)* and *-lay*, and the alternants of *-na-po* and *-nun-moyang-i* are in their docstrings.

## References

* [sohn-2018]
* [aikhenvald-2004], §4.6
* [de-haan-2013]
* [lee-2011]
* [lee-2013]
* [cumming-2026]
-/

@[expose] public section

namespace Korean.Evidentiality

open Evidential Tense
open scoped Denotes

/-! ### Perceptual evidentials -/

/-- The pre-final suffix *-te*, the retrospective: firsthand information acquired before the
time of speech, by seeing, by feeling, or by inference from concrete evidence. -/
def te : Evidential.Timed :=
  { morphs := [.suff "te"], covers := {.visual, .sensory, .inference},
    acquisitionToSpeech := ⟦past⟧ }

/-- The sentence ender *-ney* in its evidential use: perception at the time of speech, through
observation, experience or inference. Without the politeness particle *-yo* it can also be the
familiar-level declarative, which marks no source. -/
def ney : Evidential.Timed :=
  { morphs := [.suff "ney"], covers := {.visual, .sensory, .inference},
    acquisitionToSpeech := ⟦present⟧ }

/-- The ender *-te-la-ko*, the declarative *-te-la* followed by the quotative particle *ko*,
fossilized as a retrospective that casts the perception as the speaker's own casual report. -/
def teLako : Evidential.Timed :=
  { morphs := [.suff "te", .suff "la", .suff "ko"], covers := {.visual, .sensory, .inference},
    acquisitionToSpeech := ⟦past⟧ }

/-- The perceptual evidentials. -/
def perceptual : List Evidential := [te.toEvidential, ney.toEvidential, teLako.toEvidential]

/-! ### Quotative and reported evidentials -/

/-- The declarative *-tay*, *-lay* after the copula or *-te*, from *-ta ko hay* 'say that':
quotative when the reporter is specified, and the one hearsay evidential when it is not. -/
def tay : Evidential := { morphs := [.suff "tay"], covers := {.hearsay, .quotative} }

/-- The interrogative *-nyay* 'X asks whether', which needs a reporter. -/
def nyay : Evidential := { morphs := [.suff "nyay"], covers := {.quotative} }

/-- The imperative *-(u)lay* 'X commands that', which needs a reporter. -/
def ulay : Evidential := { morphs := [.suff "(u)lay"], covers := {.quotative} }

/-- The propositive *-cay* 'X suggests that', which needs a reporter. -/
def cay : Evidential := { morphs := [.suff "cay"], covers := {.quotative} }

/-- The ender *-ta-mye(nse)* 'I heard that, is it true?', for information the speaker heard
indirectly and would like confirmed. -/
def tamyense : Evidential := { morphs := [.suff "ta", .suff "mye(nse)"], covers := {.hearsay} }

/-- The quotative and reported evidentials. -/
def reported : List Evidential := [tay, nyay, ulay, cay, tamyense]

/-! ### Inferential evidentials -/

/-- The phrasal suffix *-na-po* 'it seems, it looks like', with its free variant *-(n)un-ka-po*:
inference from circumstantial sensory evidence. -/
def napo : Evidential := { morphs := [.suff "na", .suff "po"], covers := {.inference} }

/-- The phrasal suffix *-nun-moyang-i* 'it appears, it seems', with *-un* or *-ul* in place of the
relative ending *-nun*, used only when there is external circumstantial sensory evidence. -/
def moyangi : Evidential :=
  { morphs := [.suff "nun", .suff "moyang", .suff "i"], covers := {.inference} }

/-- The inferential evidentials. -/
def inferential : List Evidential := [napo, moyangi]

/-- The evidentials, by subclass in the order of their slots in the predicate. -/
def evidentials : List Evidential := inferential ++ perceptual ++ reported

end Korean.Evidentiality
