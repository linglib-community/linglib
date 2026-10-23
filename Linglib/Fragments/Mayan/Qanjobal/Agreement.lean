module

public import Linglib.Syntax.Case.Basic
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Q'anjob'al agreement

Q'anjob'al, of the Q'anjob'alan branch of Mayan, is a verb-initial language that marks person
with the two Mayan sets: Set A, prefixes with pre-consonantal and pre-vocalic shapes, indexes
the transitive subject and the possessor, and Set B the transitive object and the intransitive
subject. Set B follows the aspect marker and precedes the stem, so Q'anjob'al is a
high-absolutive language. The aspect markers are clitics, completive *(ma)x-*, incompletive
*chi-* and irrealis *(ho)q-*, unlike the auxiliaries of Chol. The alignment is ergative in every
clause with a preverbal aspect marker, the incompletive included, and Set A marks every subject
in a clause without one, such as the progressive with *lanan*. Mateo-Toledo's dissertation and
Imanishi's comparison of the splits are the sources, and Coon, Mateo Pedro and Preminger give
the paradigms.

## Main declarations

* `Qanjobal.setAExponent`, `Qanjobal.setBExponent`: the Set A markers by the following segment
  and the Set B markers.
* `Qanjobal.template`, `Qanjobal.assignCase`: the verbal complex and the case of each argument by
  aspect.

## Implementation notes

Set A on the subject of an aspectless clause is `Alignment.extendedErgative`, Coon's genitive
rather than a nominative; the descriptive grammars call the pattern nominative-accusative. The
case function sees aspect only, so the other aspectless contexts, purpose clauses and aspectless
complements among them, lie outside it.

## References

* [mateo-toledo-2008]
* [imanishi-2020]
* [coon-mateo-pedro-preminger-2014]
* [coon-2013]
-/

@[expose] public section

namespace Qanjobal

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The Q'anjob'al verbal complex has the aspect marker, Set B and Set A before the stem and the
status suffix after it ([mateo-toledo-2008]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setB, .setA], suffixSlots := [.status] }

/-- Q'anjob'al is ergative in every clause with a preverbal aspect marker, the imperfective
*chi-* included, and puts Set A on every subject in clauses without one, of which the
progressive with *lanan* is the one an aspect category names ([mateo-toledo-2008],
[imanishi-2020]); the other aspectless contexts, purpose clauses and aspectless complements
among them, lie outside the aspect vocabulary. -/
def assignCase : UD.Aspect → ArgumentRole → Case
  | .Prog => Alignment.extendedErgative
  | .Perf | .Imp | .Prosp | .Hab | .Iter => Alignment.ergative

/-! ### Person-number paradigm -/

/-- Set A (ergative/possessive) markers by following-segment
    environment ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl
    cells are discontinuous exponents: person prefix plus the free
    plural word *heb'*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "hin"]),
     (.personNumber .second .singular, [.pref "ha"]),
     (.personNumber .third .singular, [.pref "s"]), (.personNumber .first .plural, [.pref "ko"]),
     (.personNumber .second .plural, [.pref "he"]),
     (.personNumber .third .plural, [.pref "s", .free "heb'"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "w"]), (.personNumber .second .singular, [.pref "h"]),
     (.personNumber .third .singular, [.pref "y"]), (.personNumber .first .plural, [.pref "j"]),
     (.personNumber .second .plural, [.pref "hey"]),
     (.personNumber .third .plural, [.pref "y", .free "heb'"])]

/-- The Set B (absolutive) markers, suffixed to the aspect marker
([coon-mateo-pedro-preminger-2014] (13)), with a zero third person singular; the third person
plural is the free plural word *heb'* alone. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.suff "in"]), (.personNumber .second .singular, [.suff "ach"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "on"]),
   (.personNumber .second .plural, [.suff "ex"]), (.personNumber .third .plural, [.free "heb'"])]

theorem p3sg_abs_null : setBExponent.realize (.personNumber .third .singular) = some [] := rfl

theorem p3sg_erg_allomorphy :
    (setAExponent .consonant).realize (.personNumber .third .singular) = some [.pref "s"] ∧
    (setAExponent .vowel).realize (.personNumber .third .singular) = some [.pref "y"] := ⟨rfl, rfl⟩

end Qanjobal
