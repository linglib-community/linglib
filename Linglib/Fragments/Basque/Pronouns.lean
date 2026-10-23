module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Basque pronouns and allocutive markers

Basque has two pronouns for a single addressee, the familiar *hi* and the ordinary *zu*. *Zu*
was once the second person plural and still agrees as one: the verb takes the same plural
marking with *zu* as with *gu* 'we'. The newer plural *zuek* is built on it. The Souletin
dialect has allocutive suffixes on the auxiliary, *-k* and *-n* for a familiar male and female
addressee and *-zü* for an addressee spoken to with respect. The same suffixes serve as ordinary
agreement with a second person subject.

## References

* [laka-1996]
* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace Basque

/-- The honorific grades of Basque pronouns and allocutive markers, lowest first. -/
inductive Grade where
  /-- The familiar grade, *hi*. -/
  | familiar
  /-- The polite grade, *zu*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *ni* — 1sg. -/
def ni : PersonalPronoun := { form := "ni", person := some .first, number := some .singular }

/-- *gu* — 1pl. -/
def gu : PersonalPronoun := { form := "gu", person := some .first, number := some .plural }

/-- *hi* — 2sg familiar. -/
def hi : PersonalPronoun := { form := "hi", person := some .second, number := some .singular }

/-- *Zu* addresses one person and agrees as a second person plural. -/
def zu : PersonalPronoun :=
  { form := "zu", person := some .second, number := some .plural,
    referential := {.addressee} }

/-- *zuek* — 2pl. -/
def zuek : PersonalPronoun := { form := "zuek", person := some .second, number := some .plural }

/-- *hura* — 3sg. -/
def hura : PersonalPronoun := { form := "hura", person := some .third, number := some .singular }

/-- *haiek* — 3pl. -/
def haiek : PersonalPronoun := { form := "haiek", person := some .third, number := some .plural }

/-- The pronoun for a single addressee at each grade. -/
def addressee : Grade → PersonalPronoun
  | .familiar => hi
  | .polite => zu

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun := {ni, gu, hi, zu, zuek, hura, haiek}

theorem phi_zu : HasPhi.phi zu = HasPhi.phi zuek := by decide

theorem referential_zu : zu.referential = hi.referential := by decide

/-- The Souletin allocutive suffix for an addressee of each grade and gender. A familiar man takes
*-k* and a familiar woman *-n*, and an addressee of either sex spoken to with respect *-zü*. -/
def allocutive : Grade → Gender → Option Morphology.Morph
  | .familiar, .masculine => some (.suff "k")
  | .familiar, .feminine => some (.suff "n")
  | .polite, .masculine | .polite, .feminine => some (.suff "zü")
  | _, _ => none

theorem allocutive_polite : allocutive .polite .masculine = allocutive .polite .feminine := rfl

end Pronouns

end Basque
