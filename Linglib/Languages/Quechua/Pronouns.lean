module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Ancash Quechua interrogative pronouns

The Ancash Quechua interrogative pronouns *pi* 'who', *ima* 'what', *may* 'where', *imay* 'when'
and *imanaw* 'how', each with the ontological category it asks about, as Haspelmath tabulates
them. They are the bases of the indefinite series of `Quechua.Indefinites`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Quechua.Pronouns

/-- *pi* 'who' asks about a person. -/
def pi : InterrogativePronoun := { form := "pi", ontology := .person }

/-- *ima* 'what' asks about a thing. -/
def ima : InterrogativePronoun := { form := "ima", ontology := .thing }

/-- *may* 'where' asks about a place. -/
def may : InterrogativePronoun := { form := "may", ontology := .place }

/-- *imay* 'when' asks about a time. -/
def imay : InterrogativePronoun := { form := "imay", ontology := .time }

/-- *imanaw* 'how' asks about a manner. -/
def imanaw : InterrogativePronoun := { form := "imanaw", ontology := .manner }

/-- The interrogatives on which the indefinite series are built. -/
def interrogatives : Finset InterrogativePronoun := {pi, ima, may, imay, imanaw}

end Quechua.Pronouns
