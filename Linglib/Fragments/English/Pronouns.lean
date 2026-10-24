module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Demonstrative
public import Linglib.Syntax.Category.Pronoun.Interrogative
public import Linglib.Syntax.Category.Pronoun.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# English pronouns

This file defines the English personal, reflexive, reciprocal, interrogative and demonstrative
pronouns.

The personal pronouns distinguish a nominative from an accusative form, except *you* and *it*,
and distinguish gender in the third person singular only. *You* serves one addressee or several,
and *we* makes no clusivity distinction. *They* and *them* serve a single referent as well as
several; singular *they* bears no gender feature, where *he*, *she* and *it* each bear one. Every
personal pronoun has a reflexive in *-self* or *-selves*, singular *they* having *themself*
beside *themselves*. The reciprocals *each other* and *one another* are two-part noun phrases
rather than dedicated pronouns. The interrogatives ask about a person, a thing, a place, a time
or a manner. The demonstratives contrast a proximal with a distal form in each number.

## Main definitions

* `English.Pronouns.pronouns` — the personal pronoun inventory
* `English.Pronouns.paradigm` — its forms for each referential category
* `English.Pronouns.reflexives`, `English.Pronouns.reciprocals`,
  `English.Pronouns.interrogatives`, `English.Pronouns.demonstratives` — the other series

## Main results

* `English.Pronouns.third_singular_of_gender` — gender is marked in the third person singular only
* `English.Pronouns.paradigm_addressee`, `English.Pronouns.paradigm_speakerAddressee`,
  `English.Pronouns.paradigm_others_subset` — the forms do not distinguish the number of
  addressees or clusivity, and the plural third person forms also serve a single referent
* `English.Pronouns.exists_reflexive` — every personal pronoun has a reflexive with its person,
  number and gender

## References

* [L. Konnelly and E. Cowper, *Gender diversity and morphosyntax: An account of singular
  they* (2020)][konnelly-cowper-2020]
* [J. E. Arnold, *Two kinds of singular they: A usage-based model* (2026)][arnold-2026]
* [M. Balhorn, *The rise of epicene they* (2004)][balhorn-2004]
-/

@[expose] public section

namespace English.Pronouns

/-! ### Personal pronouns -/

/-- The first person singular nominative *I*. -/
def i : PersonalPronoun :=
  { form := "I", person := some .first, number := some .singular, cases := {.nom} }

/-- The first person singular accusative *me*. -/
def me : PersonalPronoun :=
  { form := "me", person := some .first, number := some .singular, cases := {.acc} }

/-- The first person plural nominative *we*. -/
def we : PersonalPronoun :=
  { form := "we", person := some .first, number := some .plural, cases := {.nom} }

/-- The first person plural accusative *us*. -/
def us : PersonalPronoun :=
  { form := "us", person := some .first, number := some .plural, cases := {.acc} }

/-- The second person singular *you*, one form for both cases. -/
def you : PersonalPronoun :=
  { form := "you", person := some .second, number := some .singular, cases := {.nom, .acc} }

/-- The second person plural *you*, one form for both cases. -/
def you_pl : PersonalPronoun :=
  { form := "you", person := some .second, number := some .plural, cases := {.nom, .acc} }

/-- The third person singular masculine nominative *he*. -/
def he : PersonalPronoun :=
  { form := "he", person := some .third, number := some .singular, cases := {.nom},
    gender := some .Masc }

/-- The third person singular masculine accusative *him*. -/
def him : PersonalPronoun :=
  { form := "him", person := some .third, number := some .singular, cases := {.acc},
    gender := some .Masc }

/-- The third person singular feminine nominative *she*. -/
def she : PersonalPronoun :=
  { form := "she", person := some .third, number := some .singular, cases := {.nom},
    gender := some .Fem }

/-- The third person singular feminine accusative *her*. -/
def her : PersonalPronoun :=
  { form := "her", person := some .third, number := some .singular, cases := {.acc},
    gender := some .Fem }

/-- The third person singular neuter *it*, one form for both cases. -/
def it : PersonalPronoun :=
  { form := "it", person := some .third, number := some .singular, cases := {.nom, .acc},
    gender := some .Neut }

/-- The third person plural nominative *they*. -/
def they : PersonalPronoun :=
  { form := "they", person := some .third, number := some .plural, cases := {.nom} }

/-- The third person plural accusative *them*. -/
def them : PersonalPronoun :=
  { form := "them", person := some .third, number := some .plural, cases := {.acc} }

/-- Singular *they* in the nominative, for a referent of unknown or unspecified gender and for
a person whose pronoun it is ([balhorn-2004], [arnold-2026]). It bears no gender feature
([konnelly-cowper-2020]). -/
def they_sg : PersonalPronoun :=
  { form := "they", person := some .third, number := some .singular, cases := {.nom} }

/-- Singular *they* in the accusative. -/
def them_sg : PersonalPronoun :=
  { form := "them", person := some .third, number := some .singular, cases := {.acc} }

/-- The personal pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {i, me, we, us, you, you_pl, he, him, she, her, it, they, them, they_sg, them_sg}

/-- Gender is marked in the third person singular only. -/
theorem third_singular_of_gender :
    ∀ p ∈ pronouns, p.gender.isSome → p.person = some .third ∧ p.number = some .singular := by
  decide

/-- The forms of each referential category. -/
def paradigm : Person.Category → Finset String := PersonalPronoun.paradigm pronouns

/-- *You* does not distinguish one addressee from several. -/
theorem paradigm_addressee : paradigm .addressee = paradigm .addresseeOthers := by
  decide +kernel

/-- *We* does not distinguish a group with the addressee from one without. -/
theorem paradigm_speakerAddressee : paradigm .speakerAddressee = paradigm .speakerOthers := by
  decide +kernel

/-- The forms for several others, *they* and *them*, also serve a single other. -/
theorem paradigm_others_subset : paradigm .others ⊆ paradigm .other := by
  decide +kernel

/-! ### Reflexive pronouns -/

/-- The reflexive of a personal pronoun, with its person, number and gender. -/
def reflexive (p : PersonalPronoun) (form : String) : ReflexivePronoun :=
  { form, person := p.person, number := p.number, gender := p.gender }

/-- The first person singular reflexive *myself*. -/
def myself : ReflexivePronoun := reflexive me "myself"

/-- The second person singular reflexive *yourself*. -/
def yourself : ReflexivePronoun := reflexive you "yourself"

/-- The third person singular masculine reflexive *himself*. -/
def himself : ReflexivePronoun := reflexive him "himself"

/-- The third person singular feminine reflexive *herself*. -/
def herself : ReflexivePronoun := reflexive her "herself"

/-- The third person singular neuter reflexive *itself*. -/
def itself : ReflexivePronoun := reflexive it "itself"

/-- The first person plural reflexive *ourselves*. -/
def ourselves : ReflexivePronoun := reflexive us "ourselves"

/-- The second person plural reflexive *yourselves*. -/
def yourselves : ReflexivePronoun := reflexive you_pl "yourselves"

/-- The third person plural reflexive *themselves*. -/
def themselves : ReflexivePronoun := reflexive them "themselves"

/-- The reflexive *themself* of singular *they*. -/
def themself : ReflexivePronoun := reflexive them_sg "themself"

/-- The reflexive pronoun inventory. -/
def reflexives : Finset ReflexivePronoun :=
  {myself, yourself, himself, herself, itself, ourselves, yourselves, themselves, themself}

/-- Every personal pronoun has a reflexive with its person, number and gender. -/
theorem exists_reflexive :
    ∀ p ∈ pronouns, ∃ r ∈ reflexives,
      r.person = p.person ∧ r.number = p.number ∧ r.gender = p.gender := by
  decide

/-! ### Reciprocal pronouns -/

/-- The reciprocal *each other*, a two-part noun phrase. -/
def eachOther : ReciprocalPronoun := { form := "each other", strategy := .bipartiteNP }

/-- The reciprocal *one another*, a two-part noun phrase. -/
def oneAnother : ReciprocalPronoun := { form := "one another", strategy := .bipartiteNP }

/-- The reciprocal pronoun inventory. -/
def reciprocals : Finset ReciprocalPronoun := {eachOther, oneAnother}

/-! ### Interrogative pronouns -/

/-- The interrogative *who*, for persons. -/
def who : InterrogativePronoun := { form := "who", ontology := .person }

/-- The accusative *whom* of *who*. -/
def whom : InterrogativePronoun := { form := "whom", cases := {.acc}, ontology := .person }

/-- The interrogative *what*, for things. -/
def what : InterrogativePronoun := { form := "what", ontology := .thing }

/-- The interrogative *where*, for places. -/
def where_ : InterrogativePronoun := { form := "where", ontology := .place }

/-- The interrogative *when*, for times. -/
def when_ : InterrogativePronoun := { form := "when", ontology := .time }

/-- The interrogative *how*, for manners. -/
def how : InterrogativePronoun := { form := "how", ontology := .manner }

/-- The interrogative pronoun inventory. -/
def interrogatives : Finset InterrogativePronoun := {who, whom, what, where_, when_, how}

/-! ### Demonstrative pronouns -/

/-- The singular proximal demonstrative *this*. -/
def this_ : DemonstrativePronoun :=
  { form := "this", person := some .third, number := some .singular,
    deixis := Person.first.participantSets }

/-- The singular distal demonstrative *that*. -/
def that_ : DemonstrativePronoun :=
  { form := "that", person := some .third, number := some .singular,
    deixis := Person.first.participantSetsᶜ }

/-- The plural proximal demonstrative *these*. -/
def these : DemonstrativePronoun :=
  { form := "these", person := some .third, number := some .plural,
    deixis := Person.first.participantSets }

/-- The plural distal demonstrative *those*. -/
def those : DemonstrativePronoun :=
  { form := "those", person := some .third, number := some .plural,
    deixis := Person.first.participantSetsᶜ }

/-- The demonstrative pronoun inventory. -/
def demonstratives : Finset DemonstrativePronoun := {this_, that_, these, those}

end English.Pronouns
