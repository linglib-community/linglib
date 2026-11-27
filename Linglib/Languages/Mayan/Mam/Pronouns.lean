module

public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# San Juan Atitán Mam pronouns

Mam has lost the Mayan second person markers and extended the third person ones to the second
person, and it makes up the four-way distinction of the language, inclusive, exclusive, second
and third, with a set of enclitics that also separate the two first person plurals, as England's
sketch describes. In San Juan Atitán Mam, the variety Scott describes, the enclitic is *=i*, and
the personal pronouns come in two series. The independent series, used for objects and for the
subjects of non-verbal predicates, has *qini* for the first person singular, *qoy* for the
exclusive and *qo* for the inclusive plural, the enclitic *=i* itself for the second person
singular, *qi* for the second plural, no pronoun for the third singular and *qa*, the plural
marker of the language, for the third plural. The subject and possessor series, used beside
Set A and Set B agreement, differs at the first person alone: the singular and the exclusive
plural are the bare enclitic, and the inclusive has no pronoun. Whether *qi* and *qa* are words
or enclitics Scott leaves open, so the entries carry no strength.

## Main definitions

* `Mam.iDisagr`, `Mam.qini`, `Mam.qoy`, `Mam.qo`, `Mam.qi`, `Mam.qa`: the pronouns.
* `Mam.independent`, `Mam.subjPoss`: the two series by person–number cell.

## References

* [england-2017]
* [scott-2023]
-/

@[expose] public section

namespace Mam

open Agreement

/-! ### The pronouns -/

/-- The enclitic *=i*, the second person singular pronoun and the reduced first person
singular and exclusive plural, underspecified for person and number. -/
def iDisagr : PersonalPronoun := { form := "=i", person := none, number := none }

/-- The independent first person singular *qini*. -/
def qini : PersonalPronoun := { form := "qini", person := some .first, number := some .singular }

/-- The independent first person plural exclusive *qoy*. -/
def qoy : PersonalPronoun :=
  { form := "qoy", person := some .first, clusivity := some .exclusive, number := some .plural }

/-- The first person plural inclusive *qo*. -/
def qo : PersonalPronoun :=
  { form := "qo", person := some .first, clusivity := some .inclusive, number := some .plural }

/-- The second person plural *qi*. -/
def qi : PersonalPronoun := { form := "qi", person := some .second, number := some .plural }

/-- The third person plural *qa*, the plural marker of the language. -/
def qa : PersonalPronoun := { form := "qa", person := some .third, number := some .plural }

/-! ### The two series -/

/-- The independent series, with no pronoun in the third person singular. -/
def independent : Paradigm PersonalPronoun :=
  [(.personNumber .first .singular, qini),
    (.setClusivity .exclusive (.personNumber .first .plural), qoy),
    (.setClusivity .inclusive (.personNumber .first .plural), qo),
    (.personNumber .second .singular, iDisagr), (.personNumber .second .plural, qi),
    (.personNumber .third .plural, qa)]

/-- The subject and possessor series, the bare enclitic in the first person singular and
exclusive plural and no pronoun in the inclusive plural and the third person singular. -/
def subjPoss : Paradigm PersonalPronoun :=
  [(.personNumber .first .singular, iDisagr),
    (.setClusivity .exclusive (.personNumber .first .plural), iDisagr),
    (.personNumber .second .singular, iDisagr), (.personNumber .second .plural, qi),
    (.personNumber .third .plural, qa)]

end Mam
