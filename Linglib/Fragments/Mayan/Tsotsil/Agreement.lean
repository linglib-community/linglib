module

public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Tsotsil agreement

Tsotsil marks person with two sets of affixes. Set A, the prefixes *j-*, *a-* and *s-*, before a
vowel *k-*, *av-* and *y-*, indexes the transitive subject and the possessor and marks person
only; a plural person adds a suffix, *-tik* for the inclusive first person and *-ik* for the
second and the third, the exclusive first person varying by dialect. Set B, which indexes the
intransitive subject and the transitive object, has two subsets: the suffixes *-on*, *-ot* and
zero, with the plurals *-otik*, *-oxuk* and *-ik*, and the prefixes *i-*, *a-* and zero, which
appear only after a verbal aspect prefix and never before the second person Set A, so *l-i-tal*
'I came' has the prefix and *tal-em-on* 'I have come' the suffix. The alignment is ergative in
every aspect. The verbal complex in citation order runs aspect, Set A, stem, Set B. Polian's
sketch of Tseltal and Tsotsil and Aissen's clause-structure monograph are the sources.

## Main definitions

* `Tsotsil.setAExponent`, `Tsotsil.setAPlural`, `Tsotsil.setBExponent`,
  `Tsotsil.setBPrefixExponent`: the paradigms.
* `Tsotsil.template`, `Tsotsil.assignCase`: the verbal complex and the ergative case function.

## Implementation notes

The template records the citation order with Set B after the stem; the prefixal subset, whose
distribution is dialectally heterogeneous, is a second paradigm rather than a second template.

## References

* [polian-2017b]
* [aissen-1987]
* [aissen-polian-2025]
-/

@[expose] public section

namespace Tsotsil

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the verbal complex in citation order, the aspect marker and Set A
before the stem and Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setA], suffixSlots := [.setB] }

/-- Tsotsil is ergative in every aspect. -/
def assignCase : UD.Aspect → ArgumentRole → Case := fun _ ↦ Alignment.ergative

/-! ### The paradigms -/

/-- The Set A markers by the following segment, the same prefix in both numbers since Set A
marks person alone. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "j"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "s"]), (.personNumber .first .plural, [.pref "j"]),
     (.personNumber .second .plural, [.pref "a"]), (.personNumber .third .plural, [.pref "s"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "k"]), (.personNumber .second .singular, [.pref "av"]),
     (.personNumber .third .singular, [.pref "y"]), (.personNumber .first .plural, [.pref "k"]),
     (.personNumber .second .plural, [.pref "av"]), (.personNumber .third .plural, [.pref "y"])]

/-- The plural suffix that goes with a Set A prefix, *-tik* for the inclusive first person and
*-ik* for the second and the third; the exclusive first person varies by dialect and is not
recorded. -/
def setAPlural : Person → List Morphology.Morph
  | .first | .firstInclusive => [.suff "tik"]
  | .second | .third => [.suff "ik"]
  | .firstExclusive => []

/-- The Set B suffixes, with a zero third person singular and the plural *-ik* alone in the
third person; *-on* and *-otik* have the harmonic variants *-un* and *-utik*. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.suff "on"]), (.personNumber .second .singular, [.suff "ot"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "otik"]),
   (.personNumber .second .plural, [.suff "oxuk"]), (.personNumber .third .plural, [.suff "ik"])]

/-- The Set B prefixes, used only after a verbal aspect prefix and never before the second
person Set A: *i-*, *a-* and zero, the inclusive first person plural *ij-*, the second plural
*a-* with *-ik*, and the third plural *-ik* alone. -/
def setBPrefixExponent : ExponentTable :=
  [(.personNumber .first .singular, [.pref "i"]), (.personNumber .second .singular, [.pref "a"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.pref "ij"]),
   (.personNumber .second .plural, [.pref "a", .suff "ik"]),
   (.personNumber .third .plural, [.suff "ik"])]

end Tsotsil
