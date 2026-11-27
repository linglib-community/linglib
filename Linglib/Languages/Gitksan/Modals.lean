module

public import Linglib.Semantics.Modality.Typology

/-!
# Gitksan modals

The modal system of Gitksan (Tsimshianic, ISO 639-3 `git`) as described in [matthewson-2013],
building on [peterson-2010]'s account of the epistemics. Every modal is specified for modality
type. The epistemic modals are the second-position clitics *ima('a)* and the reportative *g̱at*,
each compatible with contexts supporting possibility and necessity claims alike. The
circumstantial modals are clause-initial verbs and a predicative particle: *da'aḵhlxw*, general
circumstantial possibility; *anooḵ*, deontic possibility; and *sgi*, circumstantial (weak)
necessity.

| type           | subtype     | possibility   | (weak) necessity |
|----------------|-------------|---------------|------------------|
| circumstantial | plain       | *da'aḵhlxw*   | *sgi*            |
| circumstantial | deontic     | *anooḵ*       | *sgi*            |
| epistemic      | plain       | *ima('a)*     | *ima('a)*        |
| epistemic      | reportative | *g̱at*         | *g̱at*            |

## Implementation notes

* Forms follow [matthewson-2013] in the orthography of Hindle and Rigsby, with the underline
  marking a uvular written as a combining macron below and the glottal apostrophe as ASCII `'`.
* The library's circumstantial flavor covers the pure circumstantial, ability and teleological
  readings the paper distinguishes.
* *g̱at*'s reportative evidence requirement is not recorded: `ModalItem` has no information
  source, and the epistemic flavor covers both clitics.

## References

* [matthewson-2013]
* [peterson-2010]
* [matthewson-2016]
-/

@[expose] public section

namespace Gitksan

open Modality

/-- The plain epistemic clitic *ima('a)*, felicitous in contexts supporting possibility and
necessity claims alike. -/
def imaa : ModalItem := ⟨"ima('a)", {.possibility, .necessity} ×ˢ {.epistemic}, .neutral⟩

/-- The reportative epistemic clitic *g̱at*, felicitous only on reported evidence and, like
*ima('a)*, in contexts supporting either force. -/
def gat : ModalItem := ⟨"g̱at", {.possibility, .necessity} ×ˢ {.epistemic}, .neutral⟩

/-- The circumstantial possibility verb *da'aḵhlxw*: pure circumstantial and ability readings,
and, acceptable but not preferred, the priority readings, teleological, bouletic and deontic,
where it competes with *anooḵ*. -/
def daakhlxw : ModalItem :=
  ⟨"da'aḵhlxw", {.possibility} ×ˢ {.circumstantial, .deontic, .bouletic}, .neutral⟩

/-- The deontic possibility verb *anooḵ*, 'allow'. -/
def anook : ModalItem := ⟨"anooḵ", {.possibility} ×ˢ {.deontic}, .neutral⟩

/-- The circumstantial (weak) necessity particle *sgi*: deontic, non-deontic circumstantial,
teleological and bouletic readings, of strong and of weak necessity. -/
def sgi : ModalItem :=
  ⟨"sgi", {.necessity, .weakNecessity} ×ˢ {.deontic, .circumstantial, .bouletic}, .neutral⟩

/-- The modal inventory of [matthewson-2013]. -/
def modals : List ModalItem := [imaa, gat, daakhlxw, anook, sgi]

end Gitksan
