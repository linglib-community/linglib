module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Categories

/-!
# Hindi-Urdu pronouns

The personal pronouns of Hindi-Urdu show a three-level honorific contrast in the second person
(*tuu* / *tum* / *aap*) and demonstrative-based third-person forms (*vah* / *ve*). *Tuu* and
*tum* are historically the singular and the plural of the second person and are now, in Kachru's
terms, its intimate and its familiar form for an addressee, each keeping the agreement of its
number; *aap* is the honorific form. *Tum* and *aap* thus agree as plurals and denote one
addressee as well as several (`HindiUrdu.Pronouns.addressee_mem_referential`). There is no
allocutive agreement; an honorific subject co-opts plural verb agreement, as Alok and Bhalla
describe for Hindi ((48)).

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
* [kachru-2006]
-/

@[expose] public section

namespace HindiUrdu

/-- The honorific grades of the Hindi-Urdu second person, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *tuu*. -/
  | nonhonorific
  /-- The honorific grade, *tum*. -/
  | honorific
  /-- The high honorific grade, *aap*. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun := { form := "maiṃ", person := some .first, number := some .singular }

/-- *ham* — 1pl. -/
def ham : PersonalPronoun := { form := "ham", person := some .first, number := some .plural }

/-- *tuu* — 2sg nonhonorific. -/
def tuu : PersonalPronoun := { form := "tuu", person := some .second, number := some .singular }

/-- *tum*, the honorific second person: historically the plural, with plural agreement, for one
addressee or several ([kachru-2006] §4.3.1). -/
def tum : PersonalPronoun :=
  { form := "tum", person := some .second, number := some .plural,
    cells := {.personNumber .second .singular, .personNumber .second .plural} }

/-- *aap*, the high honorific second person, with plural agreement, for one addressee or
several. -/
def aap : PersonalPronoun :=
  { form := "aap", person := some .second, number := some .plural,
    cells := {.personNumber .second .singular, .personNumber .second .plural} }

/-- *vah* — 3sg, the distal demonstrative. -/
def vah : PersonalPronoun := { form := "vah", person := some .third, number := some .singular }

/-- *ve* — 3pl, the distal demonstrative plural. -/
def ve : PersonalPronoun := { form := "ve", person := some .third, number := some .plural }

/-- The pronoun for one addressee at each grade. -/
def addressee : Grade → PersonalPronoun
  | .nonhonorific => tuu
  | .honorific => tum
  | .highHonorific => aap

/-- The pronoun inventory. -/
def personal : Finset PersonalPronoun := {maiN, ham, tuu, tum, aap, vah, ve}

/-- Every person and number has a pronoun. -/
theorem forms_nonempty :
    ∀ c ∈ Agreement.Bundle.personNumberCells, (PersonalPronoun.forms personal c).Nonempty := by
  decide +kernel

/-- *tum* and *aap* denote one addressee, which their plural agreement does not realize. -/
theorem addressee_mem_referential :
    ∀ p ∈ ({tum, aap} : Finset PersonalPronoun),
      Person.Category.addressee ∈ p.referential ∧
        Person.Category.addressee ∉ p.agreement.categories := by
  decide +kernel

end Pronouns

end HindiUrdu
