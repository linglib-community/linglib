module

public import Linglib.Syntax.Case.Basic
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Category.Pronoun.Personal
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
their function. The independent pronouns are the Set B forms
in the first and second persons, *in*, *at*, *oj*, *ix* and the honorific *laal* and *alaq*, and
*are'* and *a're'* in the third, usually with a determiner. Can Pixabaj's sketch and Mondloch's
grammar are the sources.

## Main definitions

* `Kiche.setAExponent`, `Kiche.setBExponent`: the two paradigms.
* `Kiche.laEncl`, `Kiche.alaqEncl`: the honorific second person enclitics.
* `Kiche.template`, `Kiche.assignCase`: the verbal complex and the ergative case function.
* `Kiche.pronouns`: the independent pronouns.

## Main results

* `Kiche.addressee_honorific`: the honorific second person denotes what the nonhonorific one
  does and agrees as the third person singular.

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
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setB, .setA], [.status]⟩

/-- K'iche' is ergative in every aspect. -/
def assignCase : UD.Aspect → ArgumentRole → Case := fun _ ↦ Alignment.ergative

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

/-! ### Independent pronouns -/

/-- The honorific grades of the K'iche' second person, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *at* and *ix*. -/
  | nonhonorific
  /-- The honorific grade, *laal* and *alaq*. -/
  | honorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

/-- The first person singular *in*. -/
def in_ : PersonalPronoun := { form := "in", person := some .first, number := some .singular }

/-- The second person singular *at*. -/
def at_ : PersonalPronoun := { form := "at", person := some .second, number := some .singular }

/-- The honorific second person singular *laal*. It agrees as a third person singular and
denotes the addressee. -/
def laal : PersonalPronoun :=
  { form := "laal", person := some .third, number := some .singular, referential := {.addressee} }

/-- The third person singular *are'*, usually with a determiner, *ri are'*. -/
def are' : PersonalPronoun := { form := "are'", person := some .third, number := some .singular }

/-- The first person plural *oj*. -/
def oj : PersonalPronoun := { form := "oj", person := some .first, number := some .plural }

/-- The second person plural *ix*. -/
def ix : PersonalPronoun := { form := "ix", person := some .second, number := some .plural }

/-- The honorific second person plural *alaq*. It agrees as a third person singular and
denotes the addressee with others. -/
def alaq : PersonalPronoun :=
  { form := "alaq", person := some .third, number := some .singular,
    referential := {.addresseeOthers} }

/-- The third person plural *a're'*, usually with a determiner, *ri a're'*. -/
def a're' : PersonalPronoun := { form := "a're'", person := some .third, number := some .plural }

/-- The second person singular at each grade. -/
def addresseeSg : Grade → PersonalPronoun
  | .nonhonorific => at_
  | .honorific => laal

/-- The second person plural at each grade. -/
def addresseePl : Grade → PersonalPronoun
  | .nonhonorific => ix
  | .honorific => alaq

/-- The honorific second person denotes what the nonhonorific one does and agrees as the third
person singular *are'* does. -/
theorem addressee_honorific :
    laal.referential = at_.referential ∧ alaq.referential = ix.referential ∧
      phi laal = phi are' ∧ phi alaq = phi are' := by
  decide

/-- The independent pronouns. -/
def pronouns : Finset PersonalPronoun := {in_, at_, laal, are', oj, ix, alaq, a're'}

end Kiche
