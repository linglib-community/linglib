module

public import Linglib.Syntax.Case.Basic
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Yucatec Maya agreement

Yucatec person markers fall into two sets. Set A, the prefixes *in(w)-*, *a(w)-* and *u(y)-*
with the plural *k-* and the suffixes *-e'ex* and *-o'ob'*, marks transitive subjects,
intransitive subjects in the incompletive status and possessors; Set B, the suffixes *-en*,
*-ech*, zero, *-o'on*, *-e'ex* and *-o'ob'*, marks transitive objects, intransitive subjects in
the completive and dependent statuses and the subjects of stative predicates. The prevocalic
Set A forms carry the glides *w* and *y*, and the second and third person plurals are
discontinuous, the singular prefix with a plural suffix. The verbal complex runs aspect, Set A,
root, status, Set B, *táan u-muk-ik-en* 's/he is burying me', so Set B follows the stem and
Yucatec is a low-absolutive language. Hofling's comparative sketch of the Yucatecan languages
is the source.

## Main definitions

* `Yukatek.setAExponent`, `Yukatek.setBExponent`: the Set A and Set B paradigms.
* `Yukatek.template`, `Yukatek.assignCase`: the verbal complex and the case of each argument by
  aspect, ergative in the completive and extended ergative elsewhere.

## Implementation notes

The paradigms use the exclusive first person plural; the inclusive adds *-e'ex*. The Agent
Focus construction, which Yucatecan marks by the absence of the expected morphology rather
than by a morpheme, is not recorded.

## References

* [hofling-2017]
* [aissen-2017]
* [kaufman-norman-1984]
-/

@[expose] public section

namespace Yukatek

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the Yucatec verbal complex, the aspect marker and Set A before the
stem and the status suffix and then Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setA], suffixSlots := [.status, .setB] }

/-- Yucatec is ergative in the completive, the perfective, and puts Set A on every subject in
the incompletive aspects. -/
def assignCase : UD.Aspect → ArgumentRole → Case
  | .Perf => Alignment.ergative
  | .Imp | .Prog | .Prosp | .Hab | .Iter => Alignment.extendedErgative

/-! ### Set A -/

/-- The Set A markers by the following segment, with the glides before a vowel; the second and
third person plurals are the singular prefix with the suffixes *-e'ex* and *-o'ob'*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "in"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "u"]), (.personNumber .first .plural, [.pref "k"]),
     (.personNumber .second .plural, [.pref "a", .suff "e'ex"]),
     (.personNumber .third .plural, [.pref "u", .suff "o'ob'"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "inw"]),
     (.personNumber .second .singular, [.pref "aw"]),
     (.personNumber .third .singular, [.pref "uy"]), (.personNumber .first .plural, [.pref "k"]),
     (.personNumber .second .plural, [.pref "aw", .suff "e'ex"]),
     (.personNumber .third .plural, [.pref "uy", .suff "o'ob'"])]

/-! ### Set B -/

/-- The Set B markers, with a zero third person singular. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.suff "en"]), (.personNumber .second .singular, [.suff "ech"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "o'on"]),
   (.personNumber .second .plural, [.suff "e'ex"]), (.personNumber .third .plural, [.suff "o'ob'"])]

theorem p3sg_abs_null : setBExponent.realize (.personNumber .third .singular) = some [] := rfl

end Yukatek
