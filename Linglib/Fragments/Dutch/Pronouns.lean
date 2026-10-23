module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Dutch pronouns

This file defines the strong subject pronouns of Dutch. The third person singular distinguishes
three genders and the plural none; *wij* makes no clusivity distinction. The second person
distinguishes the familiar *jij* and *jullie* from the polite *u*, a single form for one
addressee or several that takes singular agreement.

## Main definitions

* `Dutch.Pronouns.pronouns`: the strong subject pronouns.
* `Dutch.Pronouns.addresseeSg`, `Dutch.Pronouns.addresseePl`: the pronouns of address at each
  grade.

## Main results

* `Dutch.Pronouns.addressee_number`, `Dutch.Pronouns.u_referential`: the polite grade does not
  distinguish one addressee from several, and *u* denotes what the two familiar forms denote
  together.

## References

* [ackema-neeleman-2018]
-/

@[expose] public section

namespace Dutch

/-- The honorific grades of Dutch pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *jij* and *jullie*. -/
  | familiar
  /-- The polite grade, *u*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- The first person singular *ik*. -/
def ik : PersonalPronoun :=
  { form := "ik", person := some .first, number := some .singular, cases := {.nom},
    strength := some .strong }

/-- The familiar second person singular *jij*. -/
def jij : PersonalPronoun :=
  { form := "jij", person := some .second, number := some .singular, cases := {.nom},
    strength := some .strong }

/-- The polite second person *u*, for one or several addressees, with singular agreement. -/
def u : PersonalPronoun :=
  { form := "u", person := some .second, number := some .singular, strength := some .strong,
    referential := {.addressee, .addresseeOthers} }

/-- The third person singular masculine *hij*. -/
def hij : PersonalPronoun :=
  { form := "hij", person := some .third, number := some .singular, cases := {.nom},
    gender := some .masculine, strength := some .strong }

/-- The third person singular feminine *zij*. -/
def zij_sg : PersonalPronoun :=
  { form := "zij", person := some .third, number := some .singular, cases := {.nom},
    gender := some .feminine, strength := some .strong }

/-- The third person singular neuter *het*. -/
def het : PersonalPronoun :=
  { form := "het", person := some .third, number := some .singular, gender := some .neuter,
    strength := some .strong }

/-- The first person plural *wij*. -/
def wij : PersonalPronoun :=
  { form := "wij", person := some .first, number := some .plural, cases := {.nom},
    strength := some .strong }

/-- The familiar second person plural *jullie*. -/
def jullie : PersonalPronoun :=
  { form := "jullie", person := some .second, number := some .plural, strength := some .strong }

/-- The third person plural *zij*. -/
def zij_pl : PersonalPronoun :=
  { form := "zij", person := some .third, number := some .plural, cases := {.nom},
    strength := some .strong }

/-- The pronoun for a single addressee at each grade. -/
def addresseeSg : Grade → PersonalPronoun
  | .familiar => jij
  | .polite => u

/-- The pronoun for several addressees at each grade. -/
def addresseePl : Grade → PersonalPronoun
  | .familiar => jullie
  | .polite => u

/-- The strong subject pronouns. -/
def pronouns : Finset PersonalPronoun := {ik, jij, u, hij, zij_sg, het, wij, jullie, zij_pl}

theorem addressee_number :
    addresseeSg .familiar ≠ addresseePl .familiar ∧ addresseeSg .polite = addresseePl .polite := by
  decide

theorem u_referential : u.referential = jij.referential ∪ jullie.referential := by decide

end Pronouns

end Dutch
