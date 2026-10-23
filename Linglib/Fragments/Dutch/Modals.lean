module

public import Linglib.Semantics.Modality.Basic

/-!
# Dutch modals

This file records the Dutch modal expressions of Uegaki and Hannon's elicited dataset of
force-flavour combinations, distributed with the modal typology database of Guo, Imel and
Steinert-Threlkeld. Under the projection below, *zou/zouden ... kunnen* is the one expression
whose force and flavour are not independent: it expresses epistemic necessity and epistemic
and circumstantial possibility, but not circumstantial necessity
(`Dutch.Modals.zouKunnen_not_independent`), while every other expression combines each of its
forces with each of its flavours (`Dutch.Modals.independent`).

## Implementation notes

The dataset records whether each expression is felicitous in contexts of three forces,
necessity, weak necessity and possibility, and five flavours, epistemic, deontic, teleological,
circumstantial and bouletic, with and without negation. An entry's meaning is its
positive-polarity cells judged felicitous, with weak necessity entered as necessity and
teleological as circumstantial; bouletic cells are left out, and so are the expressions with no
other felicitous cell. Whether a meaning has independent force and flavour depends on this
projection.

## References

* [W. Uegaki and E. Hannon, *Cross-linguistic dataset of force-flavour combinations in modal
  elements* (2022)][uegaki-hannon-2022]
* [Q. Guo, N. Imel and S. Steinert-Threlkeld, *A Database for Modal Semantic Typology*
  (2022)][guo-imel-steinert-threlkeld-2022]
-/

@[expose] public section

namespace Dutch.Modals

open Modality (ModalItem)

/-- *zal* 'will' expresses epistemic necessity. -/
def zal : ModalItem := { form := "zal", meaning := {(.necessity, .epistemic)} }

/-- *moet/moeten* 'must' expresses epistemic, deontic and circumstantial necessity. -/
def moetMoeten : ModalItem :=
  { form := "moet/moeten",
    meaning :=
      {(.necessity, .epistemic), (.necessity, .deontic), (.necessity, .circumstantial)} }

/-- *zou/zouden ... moeten* 'should' expresses deontic and circumstantial necessity. -/
def zouMoeten : ModalItem :=
  { form := "zou/zouden...moeten",
    meaning := {(.necessity, .deontic), (.necessity, .circumstantial)} }

/-- *kan/kunnen* 'can' expresses circumstantial possibility. -/
def kanKunnen : ModalItem :=
  { form := "kan/kunnen", meaning := {(.possibility, .circumstantial)} }

/-- *zou/zouden ... kunnen* 'could' expresses epistemic necessity and epistemic and
circumstantial possibility, but not circumstantial necessity. -/
def zouKunnen : ModalItem :=
  { form := "zou/zouden...kunnen",
    meaning :=
      {(.necessity, .epistemic), (.possibility, .epistemic), (.possibility, .circumstantial)} }

/-- *waarschijnlijk* 'probably' expresses epistemic necessity and possibility. -/
def waarschijnlijk : ModalItem :=
  { form := "waarschijnlijk", meaning := {(.necessity, .epistemic), (.possibility, .epistemic)} }

/-- *zal/zouden waarschijnlijk* 'will probably' expresses epistemic necessity. -/
def zalWaarschijnlijk : ModalItem :=
  { form := "zal/zouden waarschijnlijk", meaning := {(.necessity, .epistemic)} }

/-- *moet/moeten eigenlijk* 'should really' expresses deontic necessity. -/
def moetEigenlijk : ModalItem :=
  { form := "moet/moeten eigenlijk", meaning := {(.necessity, .deontic)} }

/-- *misschien* 'maybe' expresses epistemic possibility. -/
def misschien : ModalItem := { form := "misschien", meaning := {(.possibility, .epistemic)} }

/-- *mag/mogen* 'may' expresses deontic possibility. -/
def magMogen : ModalItem := { form := "mag/mogen", meaning := {(.possibility, .deontic)} }

/-- `inventory` lists the entries. -/
def inventory : List ModalItem :=
  [zal, moetMoeten, zouMoeten, kanKunnen, zouKunnen, waarschijnlijk,
   zalWaarschijnlijk, moetEigenlijk, misschien, magMogen]

/-- Every expression but *zou/zouden ... kunnen* combines each of its forces with each of its
flavours. -/
theorem independent :
    ∀ m ∈ inventory, m ≠ zouKunnen → ∀ f ∈ m.forces, ∀ fl ∈ m.flavors, (f, fl) ∈ m.meaning := by
  decide

theorem zouKunnen_not_independent :
    .necessity ∈ zouKunnen.forces ∧ .circumstantial ∈ zouKunnen.flavors ∧
      (.necessity, .circumstantial) ∉ zouKunnen.meaning := by
  decide

end Dutch.Modals
