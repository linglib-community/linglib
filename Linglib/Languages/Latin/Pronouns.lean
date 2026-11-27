module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Latin pronouns

The Latin interrogative *quis* 'who' is the base of most Latin indefinite pronouns, the forms of
`Languages/Latin/Indefinites.lean`, and of the distributive universal *quisque* 'each' of
`Languages/Latin/Determiners.lean`.

## References

* [haspelmath-1997]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Latin.Pronouns

/-- *quis* 'who'. -/
def quis : InterrogativePronoun := { form := "quis", ontology := .person }

end Latin.Pronouns
