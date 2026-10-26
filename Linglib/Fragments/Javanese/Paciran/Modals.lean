module

public import Linglib.Semantics.Modality.Typology

/-!
# Paciran Javanese modals

The modals of Paciran Javanese, the East Javanese dialect of Paciran village in Lamongan Regency,
as Vander Klok (2013) describes them and Vander Klok and Hohaus (2020, Table 1) tabulate them.
Every modal is specified for force, necessity or possibility, and for epistemic or root modality;
the root modals *kudu₁* and *iso* range over several root flavors. The epistemic modals are
adverbs, the root modals auxiliaries, except the main verb *kudu₂*.

| force       | epistemic | deontic | circumstantial | teleological | bouletic |
|-------------|-----------|---------|----------------|--------------|----------|
| necessity   | *mesthi*  | *kudu₁* | *kudu₁*        | *kudu₁*      | *kudu₂*  |
| possibility | *paleng*  | *oleh*  | *iso*          | *iso*        | —        |

The suffix *-NE₁* turns the strong necessity modals *mesthi* and *kudu₁* into weak necessity
modals of the same flavors, *mesthi-ne* and *kudu-ne*, and does not attach to the possibility
modals (Vander Klok and Hohaus, §4).

## Implementation notes

* The forms are ngoko, the speech level of the data and the one most used in Paciran (Vander
  Klok and Hohaus, §3.1); `register` keeps its neutral default.
* The library's circumstantial flavor covers the circumstantial and teleological columns.
* The auxiliary *kudu₁* sits above negation and resists topicalization; its homophone, the main
  verb *kudu₂*, sits below negation and topicalizes (Vander Klok and Hohaus, fn. 14).
* *-NE₁* is *-ne* after a vowel and *-e* elsewhere (§4.1). It is homophonous with the nominal
  definite clitic *-NE₂*, which Vander Klok and Hohaus treat as a distinct morpheme.

## References

* [vander-klok-2013a]
* [vander-klok-hohaus-2020]
-/

@[expose] public section

namespace Javanese.Paciran

open Modality

/-- *mesthi* is the epistemic necessity adverb. -/
def mesthi : ModalItem := ⟨"mesthi", {.necessity} ×ˢ {.epistemic}, .neutral⟩

/-- *paleng* is the epistemic possibility adverb. -/
def paleng : ModalItem := ⟨"paleng", {.possibility} ×ˢ {.epistemic}, .neutral⟩

/-- *kudu₁* is the root necessity auxiliary, with deontic, circumstantial and teleological
readings. -/
def kudu₁ : ModalItem := ⟨"kudu", {.necessity} ×ˢ {.deontic, .circumstantial}, .neutral⟩

/-- *kudu₂* is the bouletic necessity verb. -/
def kudu₂ : ModalItem := ⟨"kudu", {.necessity} ×ˢ {.bouletic}, .neutral⟩

/-- *oleh* is the deontic possibility auxiliary. -/
def oleh : ModalItem := ⟨"oleh", {.possibility} ×ˢ {.deontic}, .neutral⟩

/-- *iso* is the circumstantial possibility auxiliary, with circumstantial and teleological
readings. -/
def iso : ModalItem := ⟨"iso", {.possibility} ×ˢ {.circumstantial}, .neutral⟩

/-- `modals` is the modal system of Table 1, which leaves out the *-NE₁* forms. -/
def modals : List ModalItem := [mesthi, paleng, kudu₁, kudu₂, oleh, iso]

/-- `withNe m` is the strong necessity modal `m` suffixed with *-NE₁*, which expresses weak
necessity with the flavors of `m`. Both hosts end in a vowel and take the allomorph *-ne*. -/
def withNe (m : ModalItem) : ModalItem :=
  { m with form := m.form ++ "-ne", meaning := {.weakNecessity} ×ˢ m.flavors }

/-- *mesthi-ne* is the weak epistemic necessity adverb. -/
def mesthiNe : ModalItem := withNe mesthi

/-- *kudu-ne* is the weak root necessity adverb, built on the auxiliary *kudu₁*. -/
def kuduNe : ModalItem := withNe kudu₁

end Javanese.Paciran
