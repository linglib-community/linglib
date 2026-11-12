module

public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Syntax.Category.Pronoun.OntologicalCategory

/-!
# Interrogative pronouns

An interrogative pronoun is a pronoun with the ontological category it asks about: a person for
*who*, a thing for *what*, a place for *where*. The categories are those of the indefinite
series, which many languages build on their interrogatives, and they take in the pro-forms for
place, time, manner and reason, which surface as adverbs. The token of an interrogative is
wh-marked, with [the word class its category fixes](##InterrogativePronoun.toWord), and since
Chomsky takes a wh-phrase to be an R-expression, [it is one where it is nominal and never a
pronominal](##InterrogativePronoun.bindingClassOf_toWord).

## References

* [haspelmath-1997]
* [chomsky-1981]
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
def toWord : Morphology.Word := p.toPronoun.toWord (some .Int) (cat := p.ontology.upos)

/-- An interrogative projects a wh-marked word. -/
theorem isWh_toWord : p.toWord.features.IsWh :=
  .inl rfl

/-- An interrogative is an R-expression where its word class is nominal, as *who* is and *where*
is not, and is not a pronominal. -/
@[simp]
theorem bindingClassOf_toWord :
    Binding.bindingClassOf p.toWord =
      if Binding.IsNominal p.ontology.upos then some .rExpression else none :=
  p.toPronoun.bindingClassOf_toWord_of_isOperator (.inl rfl) _

end InterrogativePronoun
