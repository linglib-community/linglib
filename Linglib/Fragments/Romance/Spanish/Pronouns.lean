module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Spanish personal pronouns

The subject pronouns are *yo*, *tú*, *usted*, *él* and *ella* in the singular and *nosotros*,
*nosotras*, *vosotros*, *vosotras*, *ustedes*, *ellos* and *ellas* in the plural, with *vos* for
*tú* in some Latin-American countries. *Tú* and *vosotros* address familiars, *usted* and
*ustedes* others; *vosotros* is used in Spain only, and in Latin America *ustedes* is the plural of
*tú* as well as of *usted*. Descending from *Vuestra Merced* 'Your Grace', *usted* and *ustedes*
take third-person verb forms ([butt-benjamin-2019]). *Usted* is third person in its clitics and
reflexives as well, *yo la respeto (a usted)* 'I respect you', and it shows a person-case effect:
the accusative *la* of *se la presentaré a los estudiantes* 'I will introduce her to the
students' cannot refer to the addressee ([adamson-zompi-2025], after [rezac-2011]).

## References

* [adamson-zompi-2025]
* [butt-benjamin-2019]
* [rezac-2011]
-/

@[expose] public section

namespace Spanish

/-- The honorific grades of Spanish pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *tú*, *vos*, *vosotros* and *vosotras*. -/
  | familiar
  /-- The polite grade, *usted* and *ustedes*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *yo* 'I'. -/
def yo : PersonalPronoun := { form := "yo", person := some .first, number := some .singular }

/-- *tú* 'you', familiar. -/
def tu : PersonalPronoun := { form := "tú", person := some .second, number := some .singular }

/-- *vos* 'you', familiar, in some Latin-American countries. -/
def vos : PersonalPronoun := { form := "vos", person := some .second, number := some .singular }

/-- *usted* 'you', polite, with third-person agreement. -/
def usted : PersonalPronoun :=
  { form := "usted", person := some .third, number := some .singular,
    referential := {.addressee} }

/-- *él* 'he, it'. -/
def el : PersonalPronoun :=
  { form := "él", person := some .third, number := some .singular, gender := some .Masc }

/-- *ella* 'she, it'. -/
def ella : PersonalPronoun :=
  { form := "ella", person := some .third, number := some .singular, gender := some .Fem }

/-- *nosotros* 'we', masculine or mixed. -/
def nosotros : PersonalPronoun :=
  { form := "nosotros", person := some .first, number := some .plural,
    gender := some .Masc }

/-- *nosotras* 'we', feminine. -/
def nosotras : PersonalPronoun :=
  { form := "nosotras", person := some .first, number := some .plural,
    gender := some .Fem }

/-- *vosotros* 'you', familiar plural, masculine or mixed, used in Spain. -/
def vosotros : PersonalPronoun :=
  { form := "vosotros", person := some .second, number := some .plural,
    gender := some .Masc }

/-- *vosotras* 'you', familiar plural, feminine, used in Spain. -/
def vosotras : PersonalPronoun :=
  { form := "vosotras", person := some .second, number := some .plural,
    gender := some .Fem }

/-- *ustedes* 'you', plural with third-person agreement: polite in Spain, the only plural of
address in Latin America. -/
def ustedes : PersonalPronoun :=
  { form := "ustedes", person := some .third, number := some .plural,
    referential := {.addresseeOthers} }

/-- *ellos* 'they', masculine or mixed. -/
def ellos : PersonalPronoun :=
  { form := "ellos", person := some .third, number := some .plural, gender := some .Masc }

/-- *ellas* 'they', feminine. -/
def ellas : PersonalPronoun :=
  { form := "ellas", person := some .third, number := some .plural, gender := some .Fem }

/-- The pronouns for a single addressee at each grade, *vos* beside *tú* where it is used. -/
def addresseeSg : Grade → Finset PersonalPronoun
  | .familiar => {tu, vos}
  | .polite => {usted}

/-- The pronouns for several addressees at each grade in Spain, *vosotros* and *vosotras* by
gender at the familiar grade. -/
def addresseePl : Grade → Finset PersonalPronoun
  | .familiar => {vosotros, vosotras}
  | .polite => {ustedes}

/-- The subject pronouns. -/
def pronouns : Finset PersonalPronoun :=
  {yo, tu, vos, usted, el, ella, nosotros, nosotras, vosotros, vosotras, ustedes, ellos, ellas}

end Pronouns

end Spanish
