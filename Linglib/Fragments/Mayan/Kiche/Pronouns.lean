module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# K'iche' pronouns

The independent pronouns of K'iche' are the Set B agreement forms in the first and second
persons, *in*, *at*, *oj* and *ix*, and *are'* and *a're'* in the third, usually with a
determiner. The honorific second person, *laal* in the singular and *alaq* in the plural,
[agrees as a third person singular](##Kiche.Pronouns.addressee_honorific) and denotes the
addressee.

## References

* [can-pixabaj-2017]
* [mondloch-2017]
-/

@[expose] public section

namespace Kiche

/-- The honorific grades of the K'iche' second person, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *at* and *ix*. -/
  | nonhonorific
  /-- The honorific grade, *laal* and *alaq*. -/
  | honorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

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
def personal : Finset PersonalPronoun := {in_, at_, laal, are', oj, ix, alaq, a're'}

end Pronouns

end Kiche
