module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# German modal verbs

This file defines the German modal verbs as auxiliaries, entered by their infinitives: *dürfen*,
*können*, *mögen*, *müssen*, *sollen* and *wollen*, and the Konjunktiv II *sollte*. On Kratzer's
analysis a modal has a fixed force and a flavor that the context supplies, so that its meanings
are the products of its force with a set of flavors, and Steinert-Threlkeld, Imel and Guo give
German as a language whose modals specify force but not flavor. *können* expresses ability, the
possibility that something is so, and in colloquial German permission; *dürfen* permission;
*mögen* possibility, in formal registers; *müssen* necessity or compulsion and logical deduction;
*sollen* obligation; *wollen* desire or intention. *sollte* expresses a possible obligation and
logical probability, 'should' or 'ought to', and is listed apart from *sollen* for its weaker
force. The senses are Durrell's.

## Implementation notes

The senses are read as flavors in the usual way: ability as circumstantial, permission and
obligation as deontic, possibility, deduction and probability as epistemic, and desire as
bouletic. Senses that are not flavors are left out: the liking of *mögen*, the intention and
prediction of *sollen*, and the reports of *sollen* and claims of *wollen*, which are evidential.
The probability that *dürfen* expresses in its Konjunktiv II *dürfte* belongs to that form and is
not a sense of *dürfen*.

## References

* [durrell-2011]
* [kratzer-1981]
* [steinert-threlkeld-imel-guo-2023]
-/

@[expose] public section

namespace German.Modals

open Morphology (Features)

/-- The features of an infinitive, the form an entry cites. -/
def infinitive : Features := Features.of (verbForm := some .Inf)

/-- *dürfen* 'may, be allowed to' is a deontic possibility modal. -/
def duerfen : ModalAuxiliary where
  form := "dürfen"
  features := infinitive
  meaning := {.possibility} ×ˢ {.deontic}

/-- *können* 'can' is a possibility modal of ability, of epistemic possibility and, colloquially,
of permission. -/
def koennen : ModalAuxiliary where
  form := "können"
  features := infinitive
  meaning := {.possibility} ×ˢ {.circumstantial, .epistemic, .deontic}

/-- *mögen* 'may' is an epistemic possibility modal. -/
def moegen : ModalAuxiliary where
  form := "mögen"
  features := infinitive
  meaning := {.possibility} ×ˢ {.epistemic}

/-- *müssen* 'must, have to' is a necessity modal of obligation and of logical deduction. -/
def muessen : ModalAuxiliary where
  form := "müssen"
  features := infinitive
  meaning := {.necessity} ×ˢ {.deontic, .epistemic}

/-- *sollen* 'be supposed to' is a deontic necessity modal. -/
def sollen : ModalAuxiliary where
  form := "sollen"
  features := infinitive
  meaning := {.necessity} ×ˢ {.deontic}

/-- *wollen* 'want to' is a bouletic necessity modal. -/
def wollen : ModalAuxiliary where
  form := "wollen"
  features := infinitive
  meaning := {.necessity} ×ˢ {.bouletic}

/-- *sollte* 'should, ought to', the Konjunktiv II of *sollen*, is a weak necessity modal of
obligation and of logical probability. -/
def sollte : ModalAuxiliary where
  form := "sollte"
  features := Features.of (number := some .singular) (verbForm := some .Fin)
    (tense := some .Past) (mood := some .Sub)
  meaning := {.weakNecessity} ×ˢ {.deontic, .epistemic}

/-- The modal verbs. -/
def allModals : List ModalAuxiliary := [duerfen, koennen, moegen, muessen, sollen, wollen, sollte]

/-- *sollte* has the flavors of *sollen* and the epistemic one besides. -/
theorem sollen_flavors_ssubset_sollte :
    sollen.flavors ⊂ sollte.flavors := by
  decide

end German.Modals
