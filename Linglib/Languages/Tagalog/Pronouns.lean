module

public import Linglib.Languages.Tagalog.Case
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Feature.Person.Configuration

/-!
# Tagalog pronouns

Tagalog has eight personal pronouns, one for each of Cysouw's referential categories and no
two sharing a form: the speaker *ako*, the addressee *ikaw* (enclitic *ka*), a third party
*siya*, the speaker and addressee *kata*, the speaker and addressee with others *tayo*, the
speaker with others *kami*, the addressees *kayo* and the others *sila*. Each comes in three
case series: the *ang* forms for the subject, the *ng* forms for possessors and for non-subject
agents and objects, and the *sa* forms for obliques, which Himmelmann labels specifier,
possessive and locative and Kroeger nominative, genitive and dative. Schachter and Otanes
chart four persons, the first, the dual of the speaker and the addressee, the second and the
third, each with a non-plural and a plural that adds others to it: *kata* is the non-plural of
the dual and *tayo* its plural, the minimal-augmented type of Cysouw's first-person hierarchy.
They note that *kata* is obsolescent in educated Manila Tagalog, where *tayo* covers both, and
that the *kita* Himmelmann lists beside *kata* is a portmanteau of the first-person singular
*ng* form and the second-person singular *ang* form, not a dual.

## Main definitions

* `Tagalog.Pronouns.ang`, `Tagalog.Pronouns.ng`, `Tagalog.Pronouns.sa` — the three case series,
  a form for each category
* `Tagalog.Pronouns.table`, `Tagalog.Pronouns.entry`, `Tagalog.Pronouns.personal` — the forms
  of each category in each series, and the pronoun of a form with the person, clusivity, number
  and case of the cell it fills

## Main results

* `Tagalog.Pronouns.referential_entry` — a form denotes the category of its cell, which its
  person, clusivity and number realize
* `Tagalog.Pronouns.paradigm_nom` — the inventory's subject paradigm is the *ang* series
* `Tagalog.Pronouns.ang_injective` — no two categories share an *ang* form

## References

* [cysouw-2003]
* [himmelmann-2005-tagalog]
* [kroeger-1991-thesis]
* [schachter-otanes-1972]
-/

@[expose] public section

namespace Tagalog.Pronouns

open Person (Category)

/-- The number of a category: the non-plural of Schachter and Otanes's chart, the smallest
referent of its person, for a single member and for the speaker and addressee alone, and their
plural, the same "and others", for the rest. -/
def number : Category → Number
  | .speaker | .addressee | .other | .speakerAddressee => .minimal
  | .speakerAddresseeOthers | .speakerOthers | .addresseeOthers | .others => .augmented

/-- The *ang* series, the subject forms. -/
def ang : Category → String
  | .speaker => "ako"
  | .addressee => "ikaw"
  | .other => "siya"
  | .speakerAddressee => "kata"
  | .speakerAddresseeOthers => "tayo"
  | .speakerOthers => "kami"
  | .addresseeOthers => "kayo"
  | .others => "sila"

/-- The *ng* series, the forms of possessors and of non-subject agents and objects. -/
def ng : Category → String
  | .speaker => "ko"
  | .addressee => "mo"
  | .other => "niya"
  | .speakerAddressee => "nita"
  | .speakerAddresseeOthers => "natin"
  | .speakerOthers => "namin"
  | .addresseeOthers => "ninyo"
  | .others => "nila"

/-- The *sa* series, the oblique forms. -/
def sa : Category → String
  | .speaker => "akin"
  | .addressee => "iyo"
  | .other => "kaniya"
  | .speakerAddressee => "kanita"
  | .speakerAddresseeOthers => "atin"
  | .speakerOthers => "amin"
  | .addresseeOthers => "inyo"
  | .others => "kanila"

/-- The form of each category in each case series. -/
def table : Category × Case → Finset String
  | (c, .ang) => {ang c}
  | (c, .ng) => {ng c}
  | (c, .sa) => {sa c}

/-- The pronoun `f`, with the person, clusivity and number of the category whose cell it fills
and the comparative value of its series. -/
def entry : String → PersonalPronoun :=
  .ofTable (·.1.person) (·.1.clusivity) (fun x ↦ some (number x.1)) (fun _ ↦ none)
    (some ·.2.label) table

/-- The pronoun inventory: the entry of every form of the table. -/
def personal : Finset PersonalPronoun := (Finset.univ.biUnion table).image entry

/-- A form denotes exactly the category of its cell, and its person, clusivity and number realize
that category. -/
theorem referential_entry :
    ∀ x, ∀ f ∈ table x, (entry f).referential = {x.1} ∧ (entry f).IsOrdinary := by
  decide +kernel

/-- Every category has a pronoun. -/
theorem paradigm_nonempty : ∀ c, (PersonalPronoun.paradigm personal c).Nonempty := by
  decide +kernel

/-- The inventory's paradigm in a case series is the series: the subject forms are the *ang*
forms. -/
theorem paradigm_nom (c : Category) :
    PersonalPronoun.paradigm (personal.filter (.nom ∈ ·.cases)) c = {ang c} := by
  cases c <;> decide +kernel

/-- No two categories share an *ang* form. -/
theorem ang_injective : Function.Injective ang := by decide

end Tagalog.Pronouns
