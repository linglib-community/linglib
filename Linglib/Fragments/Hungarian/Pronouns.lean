module

public import Linglib.Syntax.Category.Pronoun.Interrogative
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# Hungarian pronouns

This file defines the Hungarian interrogative pronouns *ki* 'who', *mi* 'what', *milyen* 'what
kind', *melyik* 'which', *hány* 'how many' and *mennyi* 'how much', and the interrogative
pro-adverbs *hol* 'where', *hova* 'to where', *honnan* 'from where', *mikor* 'when' and
*hogy(an)* 'how'. Each is recorded with the ontological category it asks about. They are the
bases of the indefinite series of `Hungarian.Indefinites`.

The reflexive inflects for person and number, one form for each of the six cells, from *magam*
'myself' to *maguk* 'themselves', collected in `Hungarian.Pronouns.reflexives`. Hungarian has
no grammatical gender.

## References

* [haspelmath-1997]
* [kenesei-vago-fenyvesi-1998]
* [rounds-2001]
-/

@[expose] public section

namespace Hungarian.Pronouns

/-- *ki* 'who' asks about a person. -/
def ki : InterrogativePronoun := { form := "ki", ontology := .person }

/-- *mi* 'what' asks about a thing. -/
def mi : InterrogativePronoun := { form := "mi", ontology := .thing }

/-- *milyen* 'what kind' asks about a property. -/
def milyen : InterrogativePronoun := { form := "milyen", ontology := .property }

/-- *hol* 'where' asks about a place. -/
def hol : InterrogativePronoun := { form := "hol", ontology := .place }

/-- *hova* 'to where' asks about a place as a goal. -/
def hova : InterrogativePronoun := { form := "hova", ontology := .place }

/-- *honnan* 'from where' asks about a place as a source. -/
def honnan : InterrogativePronoun := { form := "honnan", ontology := .place }

/-- *mikor* 'when' asks about a time. -/
def mikor : InterrogativePronoun := { form := "mikor", ontology := .time }

/-- *hogy(an)* 'how' asks about a manner. -/
def hogy : InterrogativePronoun := { form := "hogy", ontology := .manner }

/-- *hány* 'how many' asks about an amount. -/
def hány : InterrogativePronoun := { form := "hány", ontology := .amount }

/-- *mennyi* 'how much' asks about an amount. -/
def mennyi : InterrogativePronoun := { form := "mennyi", ontology := .amount }

/-- *melyik* 'which' is a determiner. -/
def melyik : InterrogativePronoun := { form := "melyik", ontology := .determiner }

/-! ### Reflexive pronouns -/

/-- *magam* 'myself'. -/
def magam : ReflexivePronoun := { form := "magam", person := some .first, number := some .singular }

/-- *magad* 'yourself'. -/
def magad : ReflexivePronoun :=
  { form := "magad", person := some .second, number := some .singular }

/-- *maga* 'himself, herself, itself'. -/
def maga : ReflexivePronoun := { form := "maga", person := some .third, number := some .singular }

/-- *magunk* 'ourselves'. -/
def magunk : ReflexivePronoun := { form := "magunk", person := some .first, number := some .plural }

/-- *magatok* 'yourselves'. -/
def magatok : ReflexivePronoun :=
  { form := "magatok", person := some .second, number := some .plural }

/-- *maguk* 'themselves'. -/
def maguk : ReflexivePronoun := { form := "maguk", person := some .third, number := some .plural }

/-- The reflexive paradigm. -/
def reflexives : Finset ReflexivePronoun := {magam, magad, maga, magunk, magatok, maguk}

end Hungarian.Pronouns
