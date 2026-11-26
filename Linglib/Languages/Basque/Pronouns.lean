module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Pronoun.Demonstrative
public import Linglib.Syntax.Feature.Person.Participants
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Categories
public import Linglib.Semantics.Reference.Gender

/-!
# Basque pronouns and allocutive markers

Basque has two pronouns for a single addressee, the familiar *hi* and the ordinary *zu*. *Zu*
was once the second person plural and still agrees as one: the verb takes the same plural
marking with *zu* as with *gu* 'we'. The newer plural *zuek* is built on it. The Souletin
dialect has allocutive suffixes on the auxiliary, *-k* and *-n* for a familiar male and female
addressee and *-zü* for an addressee spoken to with respect. The same suffixes serve as ordinary
agreement with a second person subject.

There is no distinct third person pronoun, and the demonstratives serve as one: *hau* 'this',
close to the speaker, *hori* 'that', close to the addressee, and *hura* 'that', close to neither,
with the plurals *hauek*, *horiek* and *haiek*. *Hura* alternates in this use with the intensive
*bera*. The personal pronouns therefore leave the third person without a form
(`Basque.Pronouns.forms_nonempty_iff`).

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
    cells := {.personNumber .second .singular} }

/-- *zuek* — 2pl. -/
def zuek : PersonalPronoun := { form := "zuek", person := some .second, number := some .plural }

/-- The pronoun for a single addressee at each grade. -/
def addressee : Grade → PersonalPronoun
  | .familiar => hi
  | .polite => zu

/-- The personal pronouns, of the first and second persons. -/
def personal : Finset PersonalPronoun := {ni, gu, hi, zu, zuek}

/-- No personal pronoun is third person. -/
theorem person_ne_third : ∀ p ∈ personal, p.person ≠ some .third := by decide

/-- A person and number has a personal pronoun exactly when the person is not the third. -/
theorem forms_nonempty_iff :
    ∀ c ∈ Agreement.Bundle.personNumberCells,
      (PersonalPronoun.forms personal c).Nonempty ↔ c.person ≠ ↑Person.third := by
  decide +kernel

/-- *hau* 'this', close to the speaker. -/
def hau : DemonstrativePronoun :=
  { form := "hau", person := some .third, number := some .singular,
    deixis := Person.first.participantSets }

/-- *hori* 'that', close to the addressee. -/
def hori : DemonstrativePronoun :=
  { form := "hori", person := some .third, number := some .singular,
    deixis := Person.second.participantSets }

/-- *hura* 'that', close to neither the speaker nor the addressee, the demonstrative most used
as a third person pronoun. -/
def hura : DemonstrativePronoun :=
  { form := "hura", person := some .third, number := some .singular,
    deixis := Person.third.participantSets }

/-- *hauek* 'these', the plural of *hau*. -/
def hauek : DemonstrativePronoun :=
  { form := "hauek", person := some .third, number := some .plural,
    deixis := Person.first.participantSets }

/-- *horiek* 'those', the plural of *hori*. -/
def horiek : DemonstrativePronoun :=
  { form := "horiek", person := some .third, number := some .plural,
    deixis := Person.second.participantSets }

/-- *haiek* 'those', the plural of *hura*. -/
def haiek : DemonstrativePronoun :=
  { form := "haiek", person := some .third, number := some .plural,
    deixis := Person.third.participantSets }

/-- The demonstratives, which serve as the third person pronouns ([laka-1996]). -/
def demonstratives : Finset DemonstrativePronoun := {hau, hori, hura, hauek, horiek, haiek}

theorem agreement_zu : zu.agreement = zuek.agreement := by decide

theorem referential_zu : zu.referential = hi.referential := by decide

/-- The Souletin allocutive suffix for an addressee of each grade and gender. A familiar man takes
*-k* and a familiar woman *-n*, and an addressee of any gender spoken to with respect *-zü*. -/
def allocutive : Grade → ReferentGender → Option Morphology.Morph
  | .familiar, .male => some (.suff "k")
  | .familiar, .female => some (.suff "n")
  | .polite, .male | .polite, .female => some (.suff "zü")

theorem allocutive_polite : allocutive .polite .male = allocutive .polite .female := rfl

end Pronouns

end Basque
