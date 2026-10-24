module

public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# San Juan Atitán Mam agreement

Mam cross-references arguments with two sets of person markers that distinguish only first from
non-first person and singular from plural: Set A, the prefixes *n-* before a consonant and
*w-* before a vowel, *t-*, *q-* and *ky-*, and Set B, *chin*, *tz'=* or zero, *qo* and *chi*.
Set A indexes transitive subjects and possessors and Set B intransitive subjects; the enclitics
of `Mam.Pronouns` complete the person distinctions. In San Juan Atitán Mam, the variety Scott
describes, a transitive object is not cross-referenced: the verb carries the non-first singular
Set B *tz'=* whatever the object, which is a full pronoun, though some speakers accept agreeing
Set B for objects as a more formal variant. The marking is therefore tripartite in every aspect,
which Scott derives from an ergative and an accusative assigned by Voice and an absolutive by
Infl. Set B precedes the stem in the verbal complex,
the high-absolutive placement. England's sketch gives the ergative pattern of the other
varieties, where Set B indexes the object, with the dialectal forms of the enclitics.

## Main definitions

* `Mam.setAExponent`, `Mam.setBExponent`, `Mam.defaultSetB`: the two paradigms and the Set B
  of a transitive clause.
* `Mam.template`, `Mam.markerSet`: the verbal complex and the tripartite marking.

## References

* [scott-2023]
* [england-2017]
* [zavala-maldonado-2017]
-/

@[expose] public section

namespace Mam

open Mayan (ExponentTable MarkerSet)

/-! ### The paradigms -/

/-- The Set A markers by the following segment; only the first person singular alternates,
*n-* before a consonant and *w-* before a vowel, and *t-* and *ky-* serve the second and the
third person alike. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "n"]), (.personNumber .second .singular, [.pref "t"]),
     (.personNumber .third .singular, [.pref "t"]), (.personNumber .first .plural, [.pref "q"]),
     (.personNumber .second .plural, [.pref "ky"]), (.personNumber .third .plural, [.pref "ky"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "w"]), (.personNumber .second .singular, [.pref "t"]),
     (.personNumber .third .singular, [.pref "t"]), (.personNumber .first .plural, [.pref "q"]),
     (.personNumber .second .plural, [.pref "ky"]), (.personNumber .third .plural, [.pref "ky"])]

/-- The Set B markers; the non-first singular is *tz'=*, also zero. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.free "chin"]),
   (.personNumber .second .singular, [.procl "tz'"]),
   (.personNumber .third .singular, [.procl "tz'"]), (.personNumber .first .plural, [.free "qo"]),
   (.personNumber .second .plural, [.free "chi"]), (.personNumber .third .plural, [.free "chi"])]

/-- The Set B of a transitive clause, the non-first singular *tz'=* whatever the object. -/
def defaultSetB : List Morphology.Morph := [.procl "tz'"]

/-! ### The verbal complex and the marking -/

/-- The position classes of the verbal complex, the aspect marker, Set B and Set A before the
stem and no status suffix. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := { prefixSlots := [.aspect, .setB, .setA] }

/-- Set A on the transitive subject and Set B on the intransitive subject in every aspect; the
object is not cross-referenced, the verb carrying the default Set B whatever the object. -/
def markerSet : ArgumentRole → Option MarkerSet
  | .A => some .setA
  | .S => some .setB
  | .P | .R | .T => none

theorem isTripartite_markerSet : Alignment.IsTripartite markerSet := ⟨nofun, nofun, nofun⟩

end Mam
