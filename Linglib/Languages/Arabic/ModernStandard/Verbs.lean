module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Agreement.Paradigm

/-!
# Modern Standard Arabic verbs

The Modern Standard Arabic past tense suffixes to its stem a person marker that also marks
number and gender: *katab-tu* 'I wrote', *katab-at* 'she wrote', *katab-uu* 'they (m.) wrote'.
Ryding counts thirteen markers. The first person does not mark gender, and the dual has no first
person and one marker for both genders of the second.

## Main definitions

* `Arabic.ModernStandard.pastSuffix`: the person markers of the past tense, by cell.

## References

* [ryding-2005]
-/

@[expose] public section

open Morphology

namespace Arabic.ModernStandard

open Agreement

/-- The person markers of the past tense, by person, number and gender, as in Ryding's paradigm
of *katab-* 'wrote' ([ryding-2005] p. 443). -/
def pastSuffix : Paradigm Morph :=
  [(Bundle.personNumber .first .singular, .suff "tu"),
   ((Bundle.personNumber .second .singular).set .gender .Masc, .suff "ta"),
   ((Bundle.personNumber .second .singular).set .gender .Fem, .suff "ti"),
   ((Bundle.personNumber .third .singular).set .gender .Masc, .suff "a"),
   ((Bundle.personNumber .third .singular).set .gender .Fem, .suff "at"),
   (Bundle.personNumber .second .dual, .suff "tumaa"),
   ((Bundle.personNumber .third .dual).set .gender .Masc, .suff "aa"),
   ((Bundle.personNumber .third .dual).set .gender .Fem, .suff "ataa"),
   (Bundle.personNumber .first .plural, .suff "naa"),
   ((Bundle.personNumber .second .plural).set .gender .Masc, .suff "tum"),
   ((Bundle.personNumber .second .plural).set .gender .Fem, .suff "tunna"),
   ((Bundle.personNumber .third .plural).set .gender .Masc, .suff "uu"),
   ((Bundle.personNumber .third .plural).set .gender .Fem, .suff "na")]

theorem pastSuffix_gender_eq_bot_iff :
    ∀ c ∈ pastSuffix.cells,
      c .gender = ⊥ ↔ c .person = ↑Person.first ∨ c = .personNumber .second .dual := by
  decide

end Arabic.ModernStandard
