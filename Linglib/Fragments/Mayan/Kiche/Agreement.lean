module

public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# K'iche' agreement

K'iche' marks person with two sets of affixes on the verb. Set B, the prefixes *in-*, *at-*,
zero, *oj-*, *ix-* and *ee-*, indexes the intransitive subject, the transitive object and the
subject of a non-verbal predicate; Set A, *in-*, *a-*, *u-*, *qa-*, *i-* and *ki-* before a
consonant and *w-*, *aw-*, *r-*, *q-*, *iw-* and *k-* before a vowel, indexes the transitive
subject and the possessor of a noun, where the first person singular possessive is *nu-*. The
alignment is ergative in every aspect. The verbal complex runs aspect, Set B, Set A, stem,
status suffix, so that Set B precedes the stem and K'iche' is a high-absolutive language. The
honorific second person agrees as a third person singular, leaving the prefix slot empty, and is
marked by the enclitics *=la* in the singular and *=alaq* in the plural, after the verb whatever
their function. Can Pixabaj's sketch and Mondloch's grammar are the
sources; the independent pronouns are in `Fragments/Mayan/Kiche/Pronouns`.

## Main definitions

* `Kiche.setAExponent`, `Kiche.setBExponent`: the two paradigms.
* `Kiche.laEncl`, `Kiche.alaqEncl`: the honorific second person enclitics.
* `Kiche.template`, `Kiche.markerSet`: the verbal complex and the ergative marking.

## References

* [can-pixabaj-2017]
* [mondloch-2017]
-/

@[expose] public section

namespace Kiche

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the verbal complex, the aspect marker, Set B and Set A before the
stem and the status suffix after it. -/
def template : Morphology.Morphotactics.Template Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setB, .setA], suffixSlots := [.status] }

/-- K'iche' is ergative in every aspect. -/
def markerSet : ArgumentRole → Option Mayan.MarkerSet := Mayan.ergativeMarking

/-! ### The paradigms -/

/-- The Set A markers by the following segment. The first person singular is *in-* on the verb
and *nu-* on a possessed noun. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "in"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "u"]), (.personNumber .first .plural, [.pref "qa"]),
     (.personNumber .second .plural, [.pref "i"]), (.personNumber .third .plural, [.pref "ki"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "w"]), (.personNumber .second .singular, [.pref "aw"]),
     (.personNumber .third .singular, [.pref "r"]), (.personNumber .first .plural, [.pref "q"]),
     (.personNumber .second .plural, [.pref "iw"]), (.personNumber .third .plural, [.pref "k"])]

/-- The Set B markers, with a zero third person singular. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.pref "in"]), (.personNumber .second .singular, [.pref "at"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.pref "oj"]),
   (.personNumber .second .plural, [.pref "ix"]), (.personNumber .third .plural, [.pref "ee"])]

/-- The honorific second person singular enclitic *=la*, after the verb in both sets. -/
def laEncl : List Morphology.Morph := [.encl "la"]

/-- The honorific second person plural enclitic *=alaq*, after the verb in both sets. -/
def alaqEncl : List Morphology.Morph := [.encl "alaq"]

end Kiche
