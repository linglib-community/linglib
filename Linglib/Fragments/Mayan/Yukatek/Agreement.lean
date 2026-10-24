module

public import Linglib.Syntax.Case.Basic
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Fragments.Mayan.Yukatek.VerbClasses
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
Yucatec is a low-absolutive language. The status suffix in turn is selected by the aspect
marker, so the split of the intransitive subject follows the aspect through the status.
Hofling's comparative sketch of the Yucatecan languages and Bohnemeyer's tables of marker
functions are the sources.

## Main definitions

* `Yukatek.setAExponent`, `Yukatek.setBExponent`: the Set A and Set B paradigms.
* `Yukatek.markerSet`: the set of markers cross-referencing each argument under each status.
* `Yukatek.template`, `Yukatek.assignCase`: the verbal complex and the case of each argument by
  aspect, read off the status the aspect selects.

## Main statements

* `Yukatek.isErgative_markerSet_iff`: the marking is ergative exactly under the perfective
  statuses, Bohnemeyer's association of the split with the aspect of the status.
* `Yukatek.isErgative_assignCase_iff`: the case function has the alignment of the marking under
  the status the aspect selects.

## Implementation notes

The forms are Hofling's, with Set A as prefixes; Bohnemeyer writes Set A as proclitics and the
first person plural as *k=(...-o'n)*. The paradigms use the exclusive first person plural; the
inclusive adds *-e'ex*. The statuses are Bohnemeyer's four; Hofling's fifth, the perfect, marks
the intransitive subject with Set B too, *jóok'-a'an-ech* 'you have gone out'. The Agent Focus
form of Yucatec, a verb stem without Set A after an optional *j-*, is not recorded.

## References

* [hofling-2017]
* [bohnemeyer-2004]
-/

@[expose] public section

namespace Yukatek

open Mayan (ExponentTable MarkerSet)

/-! ### The verbal complex -/

/-- The position classes of the Yucatec verbal complex, the aspect marker and Set A before the
stem and the status suffix and then Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setA], suffixSlots := [.status, .setB] }

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

/-! ### The split -/

/-- The marker set cross-referencing each argument under each status ([bohnemeyer-2004] Table 1,
[hofling-2017] p. 692): Set A on the transitive subject, Set B on the object, and on the
intransitive subject Set A in the incompletive and Set B in the completive and the subjunctive.
The imperative marks neither subject, *jóok'-en* 'go out!', *il-ej-∅* 'see it!' ([hofling-2017]
Tables 24.54, 24.56), and R and T, outside the functions the sources list, take none. -/
def markerSet : StatusCategory → ArgumentRole → Option MarkerSet
  | .incompletive, .S | _, .A => some .setA
  | .completive, .S | .subjunctive, .S | _, .P => some .setB
  | .imperative, .S | _, .R | _, .T => none

/-- The marking is ergative exactly under the statuses of perfective aspect, the completive and
the subjunctive, Bohnemeyer's association of the split with the aspect of the status
([bohnemeyer-2004] Table 2). -/
theorem isErgative_markerSet_iff (s : StatusCategory) :
    Alignment.IsErgative (markerSet s) ↔ s.viewpointAspect = some .perfective := by
  cases s <;> decide

theorem isAccusative_markerSet_incompletive : Alignment.IsAccusative (markerSet .incompletive) :=
  ⟨rfl, nofun⟩

/-! ### Case by aspect -/

/-- The status the marker of each aspect selects ([hofling-2017] Tables 24.49, 24.50): the
completive under the perfective *t-* and *(j)-*, the incompletive under *k-*, the durative
*táan*, *suuk* 'customarily' and *ta'ay-tak* 'about to'. No marker expresses the iterative,
which is put with the incompletive. -/
def StatusCategory.ofAspect : UD.Aspect → StatusCategory
  | .Perf => .completive
  | .Imp | .Prog | .Prosp | .Hab | .Iter => .incompletive

/-- The case of each argument by aspect: ergative where the status the aspect selects puts Set B
on the intransitive subject, and extended ergative, Set A on every subject, where it puts Set
A there. -/
def assignCase (a : UD.Aspect) : ArgumentRole → Case :=
  if markerSet (.ofAspect a) .S = some .setA then Alignment.extendedErgative
  else Alignment.ergative

theorem isErgative_assignCase_iff (a : UD.Aspect) :
    Alignment.IsErgative (assignCase a) ↔ Alignment.IsErgative (markerSet (.ofAspect a)) := by
  cases a <;> decide

end Yukatek
