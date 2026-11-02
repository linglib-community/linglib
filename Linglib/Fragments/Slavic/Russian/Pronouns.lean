module

public import Linglib.Syntax.Category.Pronoun.Interrogative
public import Linglib.Syntax.Category.Pronoun.Demonstrative

/-!
# Russian pronouns

The Russian interrogative pronouns, each with the ontological category it asks about: *kto*
'who' for people and *čto* 'what' for things, as Wade describes them, and *gde* 'where', *kogda*
'when', *kak* 'how', *skol'ko* 'how much' and the determiner *kakoj*, which Haspelmath tabulates
with them. They are the bases of the indefinite series of `Russian.Indefinites`. The demonstrative
pronouns *ètot* 'this', for something close to hand, and *tot* 'that', for something further
removed, split the space at the speaker.

## References

* [haspelmath-1997]
* [wade-2020]
-/

@[expose] public section

namespace Russian.Pronouns

/-- *kto* (кто) 'who' asks about a person ([wade-2020] §121). -/
def kto : InterrogativePronoun := { form := "kto", ontology := .person }

/-- *čto* (что) 'what' asks about a thing ([wade-2020] §121). -/
def čto : InterrogativePronoun := { form := "čto", ontology := .thing }

/-- *gde* 'where' asks about a place. -/
def gde : InterrogativePronoun := { form := "gde", ontology := .place }

/-- *kogda* 'when' asks about a time. -/
def kogda : InterrogativePronoun := { form := "kogda", ontology := .time }

/-- *kak* 'how' asks about a manner. -/
def kak : InterrogativePronoun := { form := "kak", ontology := .manner }

/-- *skol'ko* 'how much' asks about an amount. -/
def skol'ko : InterrogativePronoun := { form := "skol'ko", ontology := .amount }

/-- *kakoj* 'which' is the interrogative determiner. -/
def kakoj : InterrogativePronoun := { form := "kakoj", ontology := .determiner }

/-- The interrogatives on which the indefinite series are built. -/
def interrogatives : Finset InterrogativePronoun := {kto, čto, gde, kogda, kak, skol'ko, kakoj}

/-- *ètot* (этот) 'this' refers to something close to hand ([wade-2020] §126). -/
def ètot : DemonstrativePronoun :=
  { form := "ètot", person := some .third, number := some .singular, gender := some .Masc,
    deixis := Person.first.participantSets }

/-- *tot* (тот) 'that' refers to something further removed ([wade-2020] §126). -/
def tot : DemonstrativePronoun :=
  { form := "tot", person := some .third, number := some .singular, gender := some .Masc,
    deixis := Person.first.participantSetsᶜ }

/-- The demonstrative pronouns, masculine singular. -/
def demonstratives : List DemonstrativePronoun := [ètot, tot]

end Russian.Pronouns
