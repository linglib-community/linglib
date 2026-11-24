module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Yakut interrogative pronouns

The Yakut interrogative pronouns *kim* 'who', *tuox* 'what', *xanna* 'where', *xahan* 'when',
*xajdax* 'how' and the determiner *xannyk* 'which', each with the ontological category it asks
about, as Haspelmath tabulates them. They are the bases of the indefinite series of
`Yakut.Indefinites`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Yakut.Pronouns

/-- *kim* 'who' asks about a person. -/
def kim : InterrogativePronoun := { form := "kim", ontology := .person }

/-- *tuox* 'what' asks about a thing. -/
def tuox : InterrogativePronoun := { form := "tuox", ontology := .thing }

/-- *xanna* 'where' asks about a place. -/
def xanna : InterrogativePronoun := { form := "xanna", ontology := .place }

/-- *xahan* 'when' asks about a time. -/
def xahan : InterrogativePronoun := { form := "xahan", ontology := .time }

/-- *xajdax* 'how' asks about a manner. -/
def xajdax : InterrogativePronoun := { form := "xajdax", ontology := .manner }

/-- *xannyk* 'which' is the interrogative determiner. -/
def xannyk : InterrogativePronoun := { form := "xannyk", ontology := .determiner }

/-- The interrogatives on which the indefinite series are built. -/
def interrogatives : Finset InterrogativePronoun := {kim, tuox, xanna, xahan, xajdax, xannyk}

end Yakut.Pronouns
