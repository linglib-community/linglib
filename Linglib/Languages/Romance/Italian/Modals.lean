module

public import Linglib.Semantics.Modality.Typology

/-!
# Italian modal verbs

This file records the two core modal verbs of Italian, *potere* 'can, may' and *dovere* 'must,
have to'. Each verb has a fixed force and no fixed flavor. *Potere* expresses an ability or
another circumstantial possibility, a permission, or an epistemic possibility, and *dovere* the
corresponding necessities, with the context of use settling the reading. French *pouvoir* and
*devoir* show the same range.

## References

* [hacquard-2006]
* [hacquard-2010]
-/

@[expose] public section

namespace Italian

open Modality

/-- *potere* 'can, may' is a possibility modal with epistemic, deontic and circumstantial
readings, the last including ability. -/
def potere : ModalItem where
  form := "potere"
  meaning := {(.possibility, .epistemic), (.possibility, .deontic), (.possibility, .circumstantial)}

/-- *dovere* 'must, have to' is a necessity modal with epistemic, deontic and circumstantial
readings, the last including goal-oriented necessity. -/
def dovere : ModalItem where
  form := "dovere"
  meaning := {(.necessity, .epistemic), (.necessity, .deontic), (.necessity, .circumstantial)}

/-- The modal verbs of the fragment. -/
def modals : List ModalItem := [potere, dovere]

end Italian
