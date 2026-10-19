module

public import Linglib.Syntax.Case.Basic
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
Set B for objects as a more formal variant. The underlying case system is therefore tripartite,
an ergative from Voice, an accusative from Voice and an absolutive from Infl, visible only
through agreement, and it holds in every aspect. Set B precedes the stem in the verbal complex,
the high-absolutive placement. England's sketch gives the ergative pattern of the other
varieties, where Set B indexes the object, with the dialectal forms of the enclitics.

## Main definitions

* `Mam.setAExponent`, `Mam.setBExponent`, `Mam.defaultSetB`: the two paradigms and the Set B
  of a transitive clause.
* `Mam.template`, `Mam.assignCase`, `Mam.caseInventory`: the verbal complex, the tripartite case
  function, and the three cases it realizes.

## References

* [scott-2023]
* [england-2017]
* [zavala-maldonado-2017]
-/

@[expose] public section

namespace Mam

open Mayan (ExponentTable)

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

/-! ### The verbal complex and case -/

/-- The position classes of the verbal complex, the aspect marker, Set B and Set A before the
stem and no status suffix. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setB, .setA], []⟩

/-- Case is tripartite in every aspect, ergative on the transitive subject, accusative on the
object and absolutive on the intransitive subject. -/
def assignCase : UD.Aspect → ArgumentRole → Case := fun _ ↦ Alignment.tripartite

/-- The cases the core roles realize, the ergative, the accusative and the absolutive. -/
def caseInventory : Finset Case := ArgumentRole.core.image (assignCase .Perf)

end Mam
