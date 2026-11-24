module

public import Linglib.Semantics.Modality.Typology

/-!
# French modal verbs

This file records the core modal expressions of French. *Pouvoir* 'can, may' is a possibility
modal that expresses an ability or another circumstantial possibility, a permission, or an
epistemic possibility, and *devoir* 'must, have to' expresses the corresponding necessities, with
the context of use settling the reading. *Falloir* 'be necessary' is an impersonal necessity
verb, and *il est possible de* 'it is possible to' an impersonal possibility construction with
an infinitive. In the conditional, *devoir* expresses weak necessity, *tu devrais partir* 'you
should leave' beside *tu dois partir* 'you must leave'. Italian *potere* and *dovere* show the
same range as *pouvoir* and *devoir*.

## References

* [hacquard-2006]
* [hacquard-2010]
* [ruytenbeek-etal-2017]
* [agha-jeretic-2022]
-/

@[expose] public section

namespace French

open Modality

/-- *pouvoir* 'can, may' is a possibility modal with epistemic, deontic and circumstantial
readings, the last including ability. -/
def pouvoir : ModalItem where
  form := "pouvoir"
  meaning := {(.possibility, .epistemic), (.possibility, .deontic), (.possibility, .circumstantial)}

/-- *devoir* 'must, have to' is a necessity modal with epistemic, deontic and circumstantial
readings, the last including goal-oriented necessity. -/
def devoir : ModalItem where
  form := "devoir"
  meaning := {(.necessity, .epistemic), (.necessity, .deontic), (.necessity, .circumstantial)}

/-- *devoir* in the conditional, as in *tu devrais partir*, expresses weak necessity in each
flavor of *devoir*. -/
def devoirConditional : ModalItem where
  form := "devrait"
  meaning := devoir.meaning.image fun ff ↦ (.weakNecessity, ff.flavor)

/-- *falloir* 'be necessary' is an impersonal necessity verb with deontic and circumstantial
readings. -/
def falloir : ModalItem where
  form := "falloir"
  meaning := {(.necessity, .deontic), (.necessity, .circumstantial)}

/-- *il est possible de* 'it is possible to' is an impersonal possibility construction with an
infinitive, with deontic and circumstantial readings. -/
def ilEstPossibleDe : ModalItem where
  form := "il est possible de"
  meaning := {(.possibility, .deontic), (.possibility, .circumstantial)}

/-- The modal expressions of the fragment. -/
def modals : List ModalItem := [pouvoir, devoir, devoirConditional, falloir, ilEstPossibleDe]

end French
