module

public import Linglib.Semantics.Modality.Typology

/-!
# Hungarian modals

The Hungarian modal expressions of Uegaki and Hannon's elicited dataset of force-flavor
combinations, as distributed with the modal typology database of Guo, Imel and
Steinert-Threlkeld.

## Implementation notes

* The dataset records whether each expression is felicitous in contexts of three forces,
  necessity, weak necessity and possibility, and five flavors, epistemic, deontic, teleological,
  circumstantial and bouletic, with and without negation. An entry's meaning is its
  positive-polarity cells judged felicitous, with weak necessity entered as necessity and
  teleological as circumstantial; bouletic cells are left out, and so are the expressions with
  no other felicitous cell.
* Three forms are in standard spelling where the dataset writes otherwise: *kellene* for
  *kellne*, *-hat* ~ *-het* for *-het-* and *kép-* for *kep-*.

## References

* [uegaki-hannon-2022]
* [guo-imel-steinert-threlkeld-2022]
-/

@[expose] public section

namespace Hungarian

open Modality

/-- The auxiliary *kell* 'must' expresses epistemic, deontic and circumstantial necessity. -/
def kell : ModalItem :=
  { form := "kell", meaning := {.necessity} ×ˢ {.epistemic, .deontic, .circumstantial} }

/-- *kellene*, *kell* with the conditional suffix, 'should', expresses deontic and
circumstantial necessity. -/
def kellene : ModalItem :=
  { form := "kellene", meaning := {.necessity} ×ˢ {.deontic, .circumstantial} }

/-- *muszáj* 'have to' expresses deontic and circumstantial necessity. -/
def muszáj : ModalItem :=
  { form := "muszáj", meaning := {.necessity} ×ˢ {.deontic, .circumstantial} }

/-- *valószínűleg* 'probably' expresses epistemic necessity. -/
def valószínűleg : ModalItem :=
  { form := "valószínűleg", meaning := {(.necessity, .epistemic)} }

/-- The auxiliary *lehet* expresses epistemic possibility. -/
def lehet : ModalItem := { form := "lehet", meaning := {(.possibility, .epistemic)} }

/-- The verbal suffix *-hat* ~ *-het* expresses epistemic, deontic and circumstantial
possibility. -/
def hatHet : ModalItem :=
  { form := "-hat/-het", meaning := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial} }

/-- The verb *tud-* 'can' expresses circumstantial possibility. -/
def tud : ModalItem := { form := "tud-", meaning := {(.possibility, .circumstantial)} }

/-- *kép-* expresses circumstantial possibility. -/
def kép : ModalItem := { form := "kép-", meaning := {(.possibility, .circumstantial)} }

/-- The modal inventory. -/
def modals : List ModalItem := [kell, kellene, muszáj, valószínűleg, lehet, hatHet, tud, kép]

end Hungarian
