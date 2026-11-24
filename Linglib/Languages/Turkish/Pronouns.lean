module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Turkish interrogative pronouns

This file defines the Turkish wh-phrases as Göksel and Kerslake list them: *kim* 'who', *ne*
'what', the locative *nerede* of *nere-* 'where', *hangi* 'which', *kaç* 'how many', *ne kadar*
'how much', *ne zaman* 'when', *neden* 'why' and *nasıl* 'how', each with the ontological
category it asks about. *kim* and *ne* take every inflectional suffix of a noun and stand
where the corresponding noun phrase would; *kim* as a direct object is always accusative, and
*ne* is accusative when the speaker expects the answer from a given set. The indefinite series
of `Turkish.Indefinites` are built on generic nouns rather than on these interrogatives.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [M. Haspelmath, *Indefinite Pronouns* (1997)][haspelmath-1997]
-/

@[expose] public section

namespace Turkish.Pronouns

/-- *kim* 'who' asks about a person. -/
def kim : InterrogativePronoun := { form := "kim", ontology := .person }

/-- *ne* 'what' asks about a thing. -/
def ne : InterrogativePronoun := { form := "ne", ontology := .thing }

/-- *nerede* 'where', the locative of the stem *nere-*, asks about a place. -/
def nerede : InterrogativePronoun := { form := "nerede", ontology := .place }

/-- *hangi* 'which' is a determiner. -/
def hangi : InterrogativePronoun := { form := "hangi", ontology := .determiner }

/-- *kaç* 'how many' asks about an amount. -/
def kaç : InterrogativePronoun := { form := "kaç", ontology := .amount }

/-- *ne kadar* 'how much' asks about an amount. -/
def neKadar : InterrogativePronoun := { form := "ne kadar", ontology := .amount }

/-- *ne zaman* 'when' asks about a time. -/
def neZaman : InterrogativePronoun := { form := "ne zaman", ontology := .time }

/-- *neden* 'why', beside *niye* and *niçin*, asks about a reason. -/
def neden : InterrogativePronoun := { form := "neden", ontology := .reason }

/-- *nasıl* 'how' asks about a manner. -/
def nasıl : InterrogativePronoun := { form := "nasıl", ontology := .manner }

end Turkish.Pronouns
