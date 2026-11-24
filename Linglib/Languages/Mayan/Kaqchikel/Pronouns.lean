module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Kaqchikel pronouns

The strong pronouns of Kaqchikel are *yïn*, *rat* and *rja'* in the singular and *röj*, *rïx* and
*rje'* in the plural. In the first and second persons they are the Set B agreement markers with
an initial approximant, the glide of *yïn* or the *r* of the others.

## References

* [preminger-2014]
-/

@[expose] public section

namespace Kaqchikel.Pronouns

/-- The first person singular *yïn*. -/
def yin : PersonalPronoun := { form := "yïn", person := some .first, number := some .singular }

/-- The second person singular *rat*. -/
def rat : PersonalPronoun := { form := "rat", person := some .second, number := some .singular }

/-- The third person singular *rja'*. -/
def rja' : PersonalPronoun := { form := "rja'", person := some .third, number := some .singular }

/-- The first person plural *röj*. -/
def roj : PersonalPronoun := { form := "röj", person := some .first, number := some .plural }

/-- The second person plural *rïx*. -/
def rix : PersonalPronoun := { form := "rïx", person := some .second, number := some .plural }

/-- The third person plural *rje'*. -/
def rje' : PersonalPronoun := { form := "rje'", person := some .third, number := some .plural }

/-- The strong pronouns. -/
def personal : Finset PersonalPronoun := {yin, rat, rja', roj, rix, rje'}

end Kaqchikel.Pronouns
