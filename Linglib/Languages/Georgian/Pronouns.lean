module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Georgian interrogative pronouns

This file defines the Georgian interrogative pronouns *vin* 'who', *ra* 'what' and *romeli*
'which', and the interrogative pro-adverbs *sad(a)* 'where', *rodis* 'when' and *rogor* 'how'.
Each is recorded with the ontological category it asks about. Hewitt notes that *ra* combines
only with non-human nouns and *romeli* with human and non-human nouns alike. The interrogatives
are the bases of the indefinite series of `Georgian.Indefinites`.

## References

* [haspelmath-1997]
* [hewitt-1995]
-/

@[expose] public section

namespace Georgian.Pronouns

/-- *vin* 'who' asks about a person. -/
def vin : InterrogativePronoun := { form := "vin", ontology := .person }

/-- *ra* 'what' asks about a thing. -/
def ra : InterrogativePronoun := { form := "ra", ontology := .thing }

/-- *sad(a)* 'where' asks about a place. -/
def sad : InterrogativePronoun := { form := "sad", ontology := .place }

/-- *rodis* 'when' asks about a time. -/
def rodis : InterrogativePronoun := { form := "rodis", ontology := .time }

/-- *rogor* 'how' asks about a manner. -/
def rogor : InterrogativePronoun := { form := "rogor", ontology := .manner }

/-- *romeli* 'which' is a determiner. -/
def romeli : InterrogativePronoun := { form := "romeli", ontology := .determiner }

end Georgian.Pronouns
