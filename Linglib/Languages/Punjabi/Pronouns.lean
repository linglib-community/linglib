module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Categories

/-!
# Punjabi pronouns

The second person of Punjabi has two honorific grades, *tũ* and *tusii*. *Tusii* is the second
person plural, and as Bhatia notes the honorific forms are the plural ones, so it agrees as a
plural and denotes one addressee as well as several
(`Punjabi.Pronouns.addressee_mem_referential`). The demonstrative *uh* serves both third person
numbers. Punjabi has allocutive
agreement with third person subjects only, as Kaur describes and Alok and Bhalla report; its
marker forms are not recorded here.

## References

* [alok-bhalla-2026]
* [bhatia-1993]
* [kaur-2020]
-/

@[expose] public section

namespace Punjabi

/-- The honorific grades of Punjabi pronouns, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *tũ*. -/
  | nonhonorific
  /-- The honorific grade, *tusii*. -/
  | honorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun := { form := "maiṃ", person := some .first, number := some .singular }

/-- *asiiṃ* — 1pl. -/
def asiiN : PersonalPronoun := { form := "asiiṃ", person := some .first, number := some .plural }

/-- *tũ* — 2sg nonhonorific. -/
def tuN : PersonalPronoun := { form := "tũ", person := some .second, number := some .singular }

/-- *tusii*, the second person plural, also the honorific for one addressee ([bhatia-1993]
§2.1.2.1). -/
def tusii : PersonalPronoun :=
  { form := "tusii", person := some .second, number := some .plural,
    cells := {.personNumber .second .singular, .personNumber .second .plural} }

/-- *uh* — 3sg, the distal demonstrative. -/
def uhSg : PersonalPronoun := { form := "uh", person := some .third, number := some .singular }

/-- *uh* — 3pl, the same form. -/
def uhPl : PersonalPronoun := { form := "uh", person := some .third, number := some .plural }

/-- The pronoun for one addressee at each grade. -/
def addressee : Grade → PersonalPronoun
  | .nonhonorific => tuN
  | .honorific => tusii

/-- The pronoun inventory. -/
def personal : Finset PersonalPronoun := {maiN, asiiN, tuN, tusii, uhSg, uhPl}

/-- Every person and number has a pronoun. -/
theorem forms_nonempty :
    ∀ c ∈ Agreement.Bundle.personNumberCells, (PersonalPronoun.forms personal c).Nonempty := by
  decide +kernel

/-- *tusii* denotes one addressee, which its plural agreement does not realize. -/
theorem addressee_mem_referential :
    Person.Category.addressee ∈ tusii.referential ∧
      Person.Category.addressee ∉ tusii.categories := by
  decide +kernel

end Pronouns

end Punjabi
