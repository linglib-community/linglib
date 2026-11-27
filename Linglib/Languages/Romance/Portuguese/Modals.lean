module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# Portuguese modal verbs

This file defines the six modal forms of Ferreira's square of necessities as auxiliaries. The
possibility modal *poder*, the weak necessity modal *dever* and the strong necessity modal *ter
que* each appear in the present, *pode*, *deve* and *tem que*, and in the past imperfect,
*podia*, *devia* and *tinha que*, and the past imperfect carries the same force as the present:
*ele devia estar aqui agora, mas não está* 'he ought to be here now, but he isn't' holds where
the present *deve* is odd. The data are Brazilian, and Ferreira reports no relevant difference
from the European variety. Each form takes every flavor, and the tense is the datum the square
reads, the matter of `Studies/Ferreira2023.lean`.

## Main definitions

* `Portuguese.Modals.pode`, `Portuguese.Modals.deve`, `Portuguese.Modals.temQue`: the present
  forms.
* `Portuguese.Modals.podia`, `Portuguese.Modals.devia`, `Portuguese.Modals.tinhaQue`: the past
  imperfect forms.

## References

* [ferreira-2023]
-/

@[expose] public section

namespace Portuguese.Modals

open Modality
open Morphology (Features)

/-- The features of a present form of the third person singular. -/
def present : Features :=
  Features.of (person := some .third) (number := some .singular) (verbForm := some .Fin)
    (tense := some .Pres) (mood := some .Ind)

/-- The features of a past imperfect form of the first or the third person singular, which
share the form. -/
def imperfect : Features :=
  Features.of (number := some .singular) (verbForm := some .Fin) (tense := some .Imp)
    (mood := some .Ind)

/-! ### Present -/

/-- *pode* 'can, may', the present possibility modal. -/
def pode : ModalAuxiliary where
  form := "pode"
  meaning := {.possibility} ×ˢ Finset.univ
  features := present

/-- *deve* 'ought, should', the present weak necessity modal. -/
def deve : ModalAuxiliary where
  form := "deve"
  meaning := {.weakNecessity} ×ˢ Finset.univ
  features := present

/-- *tem que* 'must, have to', the present strong necessity modal. -/
def temQue : ModalAuxiliary where
  form := "tem que"
  meaning := {.necessity} ×ˢ Finset.univ
  features := present

/-! ### Past imperfect -/

/-- *podia* 'could, might', the past imperfect possibility modal. -/
def podia : ModalAuxiliary where
  form := "podia"
  meaning := {.possibility} ×ˢ Finset.univ
  features := imperfect

/-- *devia* 'ought', the past imperfect weak necessity modal. -/
def devia : ModalAuxiliary where
  form := "devia"
  meaning := {.weakNecessity} ×ˢ Finset.univ
  features := imperfect

/-- *tinha que* 'had to', the past imperfect strong necessity modal. -/
def tinhaQue : ModalAuxiliary where
  form := "tinha que"
  meaning := {.necessity} ×ˢ Finset.univ
  features := imperfect

end Portuguese.Modals
