module

public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Syntax.Category.Pronoun.OntologicalCategory

/-!
# Interrogative pronouns

An interrogative pronoun is a pronoun with the ontological category it asks about: a person for
*who*, a thing for *what*, a place for *where*. The categories are those of the indefinite
series, which many languages build on their interrogatives, and they take in the pro-forms for
place, time and manner, which surface as adverbs.

## Main definitions

* `InterrogativePronoun`: a pronoun with its ontological category.
* `InterrogativePronoun.toWord`: its token, wh-marked (`InterrogativePronoun.isWh_toWord`).

## References

* [haspelmath-1997]
-/

@[expose] public section

/-- An interrogative pronoun is a `Pronoun` with the ontological category it asks about. -/
@[ext]
structure InterrogativePronoun extends Pronoun where
  /-- The ontological category the form asks about. -/
  ontology : Pronoun.OntologicalCategory

instance : DecidableEq InterrogativePronoun :=
  fun _ _ ↦ decidable_of_iff _ InterrogativePronoun.ext_iff.symm

namespace InterrogativePronoun

variable (p : InterrogativePronoun)

/-- An interrogative's word is of UD pronoun type `Int`, with the word class its category
fixes. -/
def toWord : Morphology.Word :=
  { p.toPronoun.toWord (some .Int) with cat := p.ontology.upos }

/-- An interrogative projects a wh-marked word. -/
theorem isWh_toWord : p.toWord.features.IsWh :=
  .inl rfl

end InterrogativePronoun
