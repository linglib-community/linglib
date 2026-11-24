module

public import Linglib.Semantics.Modality.Typology

/-!
# Modern Greek modals

The Modern Greek modal expressions of Uegaki and Hannon's elicited dataset of force-flavor
combinations, as distributed with the modal typology database of Guo, Imel and
Steinert-Threlkeld.

## Implementation notes

The dataset records whether each expression is felicitous in contexts of three forces,
necessity, weak necessity and possibility, and five flavors, epistemic, deontic, teleological,
circumstantial and bouletic, with and without negation. An entry's meaning is its
positive-polarity cells judged felicitous, with weak necessity entered as necessity and
teleological as circumstantial; bouletic cells are left out, and so are the expressions with no
other felicitous cell.

## References

* [uegaki-hannon-2022]
* [guo-imel-steinert-threlkeld-2022]
-/

@[expose] public section

namespace Greek.StandardModern

open Modality

/-- *prepei* 'must' expresses necessity of every flavor, and epistemic possibility. -/
def prepei : ModalItem :=
  { form := "Prepei",
    meaning := {(.necessity, .epistemic), (.possibility, .epistemic), (.necessity, .deontic),
      (.necessity, .circumstantial)} }

/-- *mporei* 'can' expresses possibility of every flavor, and epistemic and circumstantial
necessity. -/
def mporei : ModalItem :=
  { form := "Mporei",
    meaning := {(.necessity, .epistemic), (.possibility, .epistemic), (.possibility, .deontic),
      (.necessity, .circumstantial), (.possibility, .circumstantial)} }

/-- *isos* 'perhaps' expresses epistemic possibility. -/
def isos : ModalItem := { form := "Isos", meaning := {(.possibility, .epistemic)} }

/-- The modal inventory. -/
def modals : List ModalItem := [prepei, mporei, isos]

end Greek.StandardModern
