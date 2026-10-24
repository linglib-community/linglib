module

public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Kaqchikel agreement

Kaqchikel (K'ichean, Mayan) cross-references both arguments of a transitive verb: the Set A
prefixes index the transitive agent, and the Set B markers the transitive patient and the
intransitive subject. The verbal complex runs aspect, Set B, Set A, stem, so Set B precedes the
stem and Kaqchikel is a high-absolutive language. Under Agent Focus the verb carries a single
marker drawn from the Set B paradigm. The alignment is ergative outside the progressive, where in
the construction with *ajin* Set A indexes the object, the inverted pattern Imanishi analyses.
Preminger's monograph is the source of the paradigms.

## Main declarations

* `Kaqchikel.setAExponent`, `Kaqchikel.setBExponent`: the Set A and Set B paradigms.
* `Kaqchikel.template`, `Kaqchikel.markerSet`: the verbal complex and the marking of the
  arguments by aspect.

## Implementation notes

The Agent Focus paradigm and the rule that predicts it are in `Studies/Preminger2014.lean`, and
the derivation of the progressive pattern in `Studies/Imanishi2014.lean`. Parenthesized segments
of the exponents drop in certain phonological contexts.

## References

* [preminger-2014]
* [imanishi-2014]
* [mondloch-2017]
-/

@[expose] public section

namespace Kaqchikel

open Mayan (ExponentTable MarkerSet)

/-! ### The verbal complex -/

/-- The Kaqchikel verbal complex has the aspect marker, Set B and Set A before the stem and the
status suffix after it ([preminger-2014]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setB, .setA], suffixSlots := [.status] }

/-- Kaqchikel is ergative in every aspect but the progressive, where in the construction with
the matrix predicate *ajin* Set A cross-references the object rather than the subject, the
inverted alignment [imanishi-2014] analyses; some varieties lack the pattern. -/
def markerSet : UD.Aspect → ArgumentRole → Option MarkerSet
  | .Prog => fun
    | .S | .A => some .setB
    | .P => some .setA
    | .R | .T => none
  | .Perf | .Imp | .Prosp | .Hab | .Iter => Mayan.ergativeMarking

/-! ### The paradigms -/

/-- The Set A markers by the following segment ([preminger-2014] (29)). The table glosses its
parenthesized segments only as dropped in certain phonological contexts; the split into
pre-consonantal and pre-vocalic shapes follows the cognate K'iche' paradigm ([mondloch-2017]).
The third person singular *ru-* has the dialectal variant *u-*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "n"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "ru"]), (.personNumber .first .plural, [.pref "qa"]),
     (.personNumber .second .plural, [.pref "i"]), (.personNumber .third .plural, [.pref "ki"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "w"]), (.personNumber .second .singular, [.pref "aw"]),
     (.personNumber .third .singular, [.pref "r"]), (.personNumber .first .plural, [.pref "q"]),
     (.personNumber .second .plural, [.pref "iw"]), (.personNumber .third .plural, [.pref "k"])]

/-- The Set B markers ([preminger-2014] (29)), with a zero third person singular. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.pref "in"]), (.personNumber .second .singular, [.pref "at"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.pref "oj"]),
   (.personNumber .second .plural, [.pref "ix"]), (.personNumber .third .plural, [.pref "e"])]

theorem isAccusative_markerSet_prog : Alignment.IsAccusative (markerSet .Prog) := ⟨rfl, nofun⟩

end Kaqchikel
