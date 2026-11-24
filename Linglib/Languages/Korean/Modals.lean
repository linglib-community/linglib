module

public import Linglib.Semantics.Modality.Typology

/-!
# Korean modals

The Korean modal expressions of Uegaki and Hannon's elicited dataset of force-flavor
combinations, as distributed with the modal typology database of Guo, Imel and
Steinert-Threlkeld.

## Implementation notes

* The dataset records whether each expression is felicitous in contexts of three forces,
  necessity, weak necessity and possibility, and five flavors, epistemic, deontic, teleological,
  circumstantial and bouletic, with and without negation. An entry's meaning is its
  positive-polarity cells judged felicitous, with weak necessity entered as necessity and
  teleological as circumstantial; bouletic cells are left out, and so are the expressions with
  no other felicitous cell.
* The doubly negated *an -myeon an-toy-* is recorded in positive clauses and has an entry; the
  singly negated expressions are recorded only under negation.

## References

* [uegaki-hannon-2022]
* [guo-imel-steinert-threlkeld-2022]
-/

@[expose] public section

namespace Korean

open Modality

/-- *-napo-* expresses epistemic necessity. -/
def napo : ModalItem := { form := "-napo-", meaning := {(.necessity, .epistemic)} }

/-- *-keyss-* expresses epistemic necessity. -/
def keyss : ModalItem := { form := "-keyss-", meaning := {(.necessity, .epistemic)} }

/-- *-ya ha-* expresses deontic and circumstantial necessity. -/
def yaHa : ModalItem :=
  { form := "-ya + ha-", meaning := {.necessity} ×ˢ {.deontic, .circumstantial} }

/-- *ke-* expresses epistemic necessity. -/
def ke : ModalItem := { form := "ke-", meaning := {(.necessity, .epistemic)} }

/-- *they-* expresses epistemic necessity. -/
def they : ModalItem := { form := "they-", meaning := {(.necessity, .epistemic)} }

/-- *-ya keyss-* expresses deontic necessity. -/
def yaKeyss : ModalItem := { form := "-ya + keyss-", meaning := {(.necessity, .deontic)} }

/-- *kes.i-coh-* 'would be good' expresses circumstantial necessity. -/
def kesiCoh : ModalItem := { form := "kes.i-coh-", meaning := {(.necessity, .circumstantial)} }

/-- *ci(-to) molun-* 'not known' expresses epistemic possibility. -/
def ciMolun : ModalItem := { form := "ci(-to) molun-", meaning := {(.possibility, .epistemic)} }

/-- *swu(-to) iss-* 'is a possibility' expresses epistemic and circumstantial possibility. -/
def swuIss : ModalItem :=
  { form := "swu(-to) iss-", meaning := {.possibility} ×ˢ {.epistemic, .circumstantial} }

/-- *-to toy-* expresses deontic and circumstantial possibility. -/
def toToy : ModalItem :=
  { form := "-to + toy-", meaning := {.possibility} ×ˢ {.deontic, .circumstantial} }

/-- The doubly negated *an -myeon an-toy-* expresses deontic necessity. -/
def anMyeonAnToy : ModalItem :=
  { form := "an -myeon an-toy-", meaning := {(.necessity, .deontic)} }

/-- The modal inventory. -/
def modals : List ModalItem :=
  [napo, keyss, yaHa, ke, they, yaKeyss, kesiCoh, ciMolun, swuIss, toToy, anMyeonAnToy]

end Korean
