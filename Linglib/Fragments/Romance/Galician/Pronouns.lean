module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Galician pronouns and allocutive clitics

Personal pronouns of Galician, with the T/V contrast *ti* / *vostede* in the
singular and *vós* / *vostedes* in the plural, and the familiar dative
clitics *che* and *vos* that double as allocutive markers ([alok-bhalla-2026]
(9)–(10)): the same morphemes serve as thematic datives, and the allocutive
use occurs in every finite embedded clause and inside infinitives.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace Galician

/-- The honorific grades of Galician pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *ti* and *vós*. -/
  | familiar
  /-- The formal grade, *vostede* and *vostedes*. -/
  | formal
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *eu* — 1sg. -/
def eu : PersonalPronoun := { form := "eu", person := some .first, number := some .singular }

/-- *nós* — 1pl. -/
def nos : PersonalPronoun := { form := "nós", person := some .first, number := some .plural }

/-- *ti* — 2sg familiar. -/
def ti : PersonalPronoun := { form := "ti", person := some .second, number := some .singular }

/-- *vostede* — 2sg formal. -/
def vostede : PersonalPronoun :=
  { form := "vostede", person := some .second, number := some .singular }

/-- *vós* — 2pl familiar. -/
def vosPl : PersonalPronoun := { form := "vós", person := some .second, number := some .plural }

/-- *vostedes* — 2pl formal. -/
def vostedes : PersonalPronoun :=
  { form := "vostedes", person := some .second, number := some .plural }

/-- *el* — 3sg masculine. -/
def el : PersonalPronoun :=
  { form := "el", person := some .third, number := some .singular, gender := some .Masc }

/-- *ela* — 3sg feminine. -/
def ela : PersonalPronoun :=
  { form := "ela", person := some .third, number := some .singular, gender := some .Fem }

/-- *eles* — 3pl masculine. -/
def eles : PersonalPronoun :=
  { form := "eles", person := some .third, number := some .plural, gender := some .Masc }

/-- *elas* — 3pl feminine. -/
def elas : PersonalPronoun :=
  { form := "elas", person := some .third, number := some .plural, gender := some .Fem }

/-- The second person singular at each grade. -/
def addresseeSg : Grade → PersonalPronoun
  | .familiar => ti
  | .formal => vostede

/-- The second person plural at each grade. -/
def addresseePl : Grade → PersonalPronoun
  | .familiar => vosPl
  | .formal => vostedes

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {eu, nos, ti, vostede, vosPl, vostedes, el, ela, eles, elas}

/-- The familiar dative clitic *che*, for a single addressee. -/
def che : Morphology.Morph := .encl "che"

/-- The familiar dative clitic *vos*, for several addressees. -/
def vos : Morphology.Morph := .encl "vos"

/-- The allocutive clitics. -/
def allocutiveClitics : List Morphology.Morph := [che, vos]

end Pronouns

end Galician
