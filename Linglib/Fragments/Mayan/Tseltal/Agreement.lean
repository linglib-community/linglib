module

public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Tseltal agreement

Tseltal marks person with two sets of affixes. Set A, the prefixes *j-*, *a-* and *s-*, before a
vowel *k-*, *aw-* and *y-*, indexes the transitive subject and the possessor and marks person
only; a plural person adds a suffix, *-tik* for the inclusive first person and *-ik* for the
second and the third, the exclusive first person varying by dialect. Set B, which indexes the
intransitive subject and the transitive object, is suffixal throughout, *-on*, *-at* and zero,
with the plurals *-otik*, *-ex* and *-ik*. The alignment is ergative in every aspect, and the
verbal complex runs aspect, Set A, stem, Set B. Polian's sketch of Tseltal and Tsotsil and
Aissen and Polian's summary of the two sets are the sources.

## Main definitions

* `Tseltal.setAExponent`, `Tseltal.setAPlural`, `Tseltal.setBExponent`: the paradigms.
* `Tseltal.template`, `Tseltal.markerSet`: the verbal complex and the ergative marking.

## References

* [polian-2017b]
* [aissen-polian-2025]
-/

@[expose] public section

namespace Tseltal

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the verbal complex, the aspect marker and Set A before the stem and
Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setA], suffixSlots := [.setB] }

/-- Tseltal is ergative in every aspect. -/
def markerSet : ArgumentRole → Option Mayan.MarkerSet := Mayan.ergativeMarking

/-! ### The paradigms -/

/-- The Set A markers by the following segment, the same prefix in both numbers since Set A
marks person alone. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "j"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "s"]), (.personNumber .first .plural, [.pref "j"]),
     (.personNumber .second .plural, [.pref "a"]), (.personNumber .third .plural, [.pref "s"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "k"]), (.personNumber .second .singular, [.pref "aw"]),
     (.personNumber .third .singular, [.pref "y"]), (.personNumber .first .plural, [.pref "k"]),
     (.personNumber .second .plural, [.pref "aw"]), (.personNumber .third .plural, [.pref "y"])]

/-- The plural suffix that goes with a Set A prefix, *-tik* for the inclusive first person and
*-ik* for the second and the third; the exclusive first person varies by dialect and is not
recorded. -/
def setAPlural : Person → List Morphology.Morph
  | .first | .firstInclusive => [.suff "tik"]
  | .second | .third => [.suff "ik"]
  | .firstExclusive => []

/-- The Set B suffixes, with a zero third person singular and the plural *-ik* alone in the
third person. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.suff "on"]), (.personNumber .second .singular, [.suff "at"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "otik"]),
   (.personNumber .second .plural, [.suff "ex"]), (.personNumber .third .plural, [.suff "ik"])]

end Tseltal
