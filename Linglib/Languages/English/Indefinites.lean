module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# English indefinite pronouns

English prefixes *some-*, *any-* and *no-* to the generic nouns *one*, *body* and *thing* and to the
interrogative *where*, so that its series mix bases. The *some-* series is used for a referent the
speaker has in mind, for one the speaker presupposes but cannot identify and for irrealis
non-specific reference, and reaches into questions and conditionals; the *any-* series takes over
from questions and conditionals through both negations and the comparative to free choice; the *no-*
series is confined to direct negation. The two longer series overlap in questions and conditionals
(*Did you see someone?*, *Did you see anyone?*). The members are those of Haspelmath's table, in
their usual spelling where he hyphenates (*some-body*).

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace English.Indefinites

/-- *someone*, of the *some-* series. -/
def someone : IndefinitePronoun := { form := "someone", ontology := .person }

/-- *anyone*, of the *any-* series. -/
def anyone : IndefinitePronoun := { form := "anyone", ontology := .person }

/-- *no one*, of the *no-* series. -/
def noOne : IndefinitePronoun := { form := "no one", ontology := .person }

/-! ### The series -/

/-- The *some-* series. -/
def someSeries : IndefinitePronoun.Series :=
  ⟨"some-", {{ form := "somebody", ontology := .person }, someone,
    { form := "something", ontology := .thing },
    { form := "somewhere", ontology := .place }, { form := "sometime", ontology := .time },
    { form := "somehow", ontology := .manner }, { form := "some", ontology := .determiner }}⟩

/-- The *any-* series. -/
def anySeries : IndefinitePronoun.Series :=
  ⟨"any-", {{ form := "anybody", ontology := .person }, anyone,
    { form := "anything", ontology := .thing },
    { form := "anywhere", ontology := .place }, { form := "anytime", ontology := .time },
    { form := "anyhow", ontology := .manner }, { form := "any", ontology := .determiner }}⟩

/-- The *no-* series, whose time and manner members are *never* and *no way*. -/
def noSeries : IndefinitePronoun.Series :=
  ⟨"no-", {{ form := "nobody", ontology := .person }, noOne,
    { form := "nothing", ontology := .thing },
    { form := "nowhere", ontology := .place }, { form := "never", ontology := .time },
    { form := "no way", ontology := .manner },
    { form := "no", ontology := .determiner }}⟩

end English.Indefinites
