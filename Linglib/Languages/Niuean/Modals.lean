module

public import Linglib.Semantics.Modality.Typology

/-!
# Niuean modals

The modals of Niuean (Polynesian, ISO 639-3 `niu`) that [matthewson-2016] §18.5 contrasts: the
general-purpose epistemic *liga*, usable in contexts of both high and low certainty, and the
circumstantial *maeke* and *lata*, specialized for possibility and for necessity. *Liga* 'likely'
is a restructuring pre-verb at the left edge of the predicate ([massam-2020] §2.5.1), and the
perfect *kua* follows it but precedes *lata* ([matthewson-quinn-talagi-2012]). *Maeke* 'possible,
able' is a raising verb, ability being one of its most frequent uses; *lata* expresses
obligation, 'should' or 'ought', and need ([massam-2020]).

## Implementation notes

* The library's circumstantial flavour covers ability and teleological readings: *maeke*'s
  ability and possibility uses and *lata*'s 'needs to' ([massam-2020] (29a)) are circumstantial,
  *lata*'s obligation reading deontic.
* No deontic use of *maeke* is attested in these sources, whose verbs of permission are
  *fakamatā* 'permit' and *toka* 'let' ([massam-2020] p. 186).

## TODO

* Check the entries against [seiter-1980]'s description of the modals, known here only through
  the examples [matthewson-2016] and [massam-2020] take from it.

## References

* [matthewson-2016]
* [massam-2020]
* [matthewson-quinn-talagi-2012]
* [seiter-1980]
-/

@[expose] public section

namespace Niuean

open Modality

/-- The epistemic pre-verb *liga* 'likely', usable in contexts of both high and low certainty
and so translated 'might', 'probably' or 'must'. -/
def liga : ModalItem := ⟨"liga", {.possibility, .necessity} ×ˢ {.epistemic}, .neutral⟩

/-- The circumstantial possibility verb *maeke* 'possible, able'. -/
def maeke : ModalItem := ⟨"maeke", {.possibility} ×ˢ {.circumstantial}, .neutral⟩

/-- The circumstantial necessity verb *lata*, of obligation, 'should' or 'ought', and of need,
'needs to'. -/
def lata : ModalItem := ⟨"lata", {.necessity} ×ˢ {.circumstantial, .deontic}, .neutral⟩

/-- The modals [matthewson-2016] §18.5 contrasts. -/
def modals : List ModalItem := [liga, maeke, lata]

end Niuean
