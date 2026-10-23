module

public import Linglib.Fragments.Tagalog.Case
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Person.Category

/-!
# Tagalog pronouns

Tagalog has eight personal pronouns, one for each of Cysouw's referential categories and no
two sharing a form: the speaker *ako*, the addressee *ikaw* (enclitic *ka*), a third party
*siya*, the speaker and addressee *kata*, the speaker and addressee with others *tayo*, the
speaker with others *kami*, the addressees *kayo* and the others *sila*. Each comes in three
case series: the *ang* forms for the subject, the *ng* forms for possessors and for non-subject
agents and objects, and the *sa* forms for obliques, which Himmelmann labels specifier,
possessive and locative and Kroeger nominative, genitive and dative. The inclusive is split
between a dual *kata* and a plural *tayo*, the minimal-augmented type of Cysouw's first-person
hierarchy. Schachter and Otanes note that the dual is obsolescent in educated Manila Tagalog,
where *tayo* covers both, and that the *kita* Himmelmann lists beside *kata* is a portmanteau
of the first-person singular *ng* form and the second-person singular *ang* form, not a dual.

## Main definitions

* `Tagalog.ang`, `Tagalog.ng`, `Tagalog.sa` — the three case series, a form for each category
* `Tagalog.entry`, `Tagalog.pronouns` — the pronoun entries, with the person and number of
  their category

## Main results

* `Tagalog.entry_categories`, `Tagalog.entry_wellFormed` — an entry denotes its category
* `Tagalog.paradigm_nom` — the inventory's subject paradigm is the *ang* series
* `Tagalog.ang_injective` — no two categories share an *ang* form

## References

* [cysouw-2003]
* [himmelmann-2005-tagalog]
* [kroeger-1991-thesis]
* [schachter-otanes-1972]
-/

@[expose] public section

namespace Tagalog

open Person (Category)

/-- The number of a category: singular for a single member, dual for the speaker and addressee
alone, and plural for the other groups. -/
def number (c : Category) : Number :=
  if c.IsSingular then .singular else if c = .speakerAddressee then .dual else .plural

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

/-- The pronoun of a category in a case series, with the series' comparative value. -/
def entry (c : Category) (k : Case) (form : String) : PersonalPronoun :=
  { form, person := some c.person, number := some (number c), cases := {k.label} }

/-- The pronoun inventory: the three series over the eight categories. -/
def pronouns : Finset PersonalPronoun :=
  Finset.univ.biUnion fun c ↦ {entry c .ang (ang c), entry c .ng (ng c), entry c .sa (sa c)}

theorem entry_categories (c : Category) (k : Case) (f : String) :
    (entry c k f).categories = {c} := by
  show Category.ofPersonNumber c.person (number c) = {c}
  cases c <;> decide

theorem entry_wellFormed (c : Category) (k : Case) (f : String) : (entry c k f).WellFormed := by
  show ∀ per ∈ some c.person, per.MarksClusivity → some (number c) ≠ some .singular
  cases c <;> decide

theorem paradigm_nom (c : Category) :
    PersonalPronoun.paradigm (pronouns.filter (.nom ∈ ·.cases)) c = {ang c} := by
  cases c <;> decide +kernel

theorem ang_injective : Function.Injective ang := by decide

end Tagalog
