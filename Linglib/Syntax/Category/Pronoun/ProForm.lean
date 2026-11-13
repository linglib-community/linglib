module

public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Proforms

Bhat divides the pronouns into the personal pronouns, which denote speech roles, and the
proforms: the interrogatives, indefinites, demonstratives and relatives. A proform has two
elements, a general term for the ontological category it stands for, a person (*who*,
*someone*), a thing (*what*, *something*), a place (*where*, *somewhere*), and a pronominal
element for its function, so that the proforms of a language line up in a table of correlatives.
This file defines the proform by its general term; the function is that of its kind,
`InterrogativePronoun` or `IndefinitePronoun`, and a `ProForm` of neither kind is an
indeterminate, whose function its particle or its clause supplies, as for Japanese *dare*. The
proforms cut across the word classes, and the category [fixes the class by
default](##ProForm.OntologicalCategory.upos). Chomsky takes wh-phrases and quantifier expressions
to be R-expressions, so the token of a proform of those types [is one where it is nominal and
never a pronominal](##ProForm.bindingClassOf_toWord).

## TODO

* `ProForm.OntologicalCategory.determiner` is a word class in Diessel's tables, not an ontological
  category; it is a row of Haspelmath's series and stays until the series tables are entered by
  word class.
* The word class of an amount proform differs across languages; the default is a pronoun's.

## References

* [bhat-2004]
* [haspelmath-1997]
* [diessel-2003]
* [chomsky-1981]
-/

@[expose] public section

/-- The ontological categories of proforms. Person, thing, property, place, time, manner and
amount are the seven Haspelmath finds most often expressed by simple means, the cut between
person and thing (*somebody* against *something*) being made nearly everywhere. Many languages
add a determiner (*which*) distinct from the substantival *who* and *what* and the adjectival
*what kind*, and some a reason (*why*), which English and German have as an interrogative but
not as an indefinite. -/
inductive ProForm.OntologicalCategory where
  /-- Person is the category of *somebody*, *someone* and interrogative *who*. -/
  | person
  /-- Thing is the category of *something* and interrogative *what*. -/
  | thing
  /-- Property or kind is the category of *some kind of* and interrogative *what kind*. -/
  | property
  /-- Place is the category of *somewhere* and interrogative *where*. -/
  | place
  /-- Time is the category of *sometime* and interrogative *when*. -/
  | time
  /-- Manner is the category of *somehow* and interrogative *how*. -/
  | manner
  /-- Amount is the category of *some amount* and interrogative *how much*. -/
  | amount
  /-- Determiner is the category of *some* N and interrogative *which*. -/
  | determiner
  /-- Reason is the category of *for some reason* and interrogative *why*. -/
  | reason
  deriving DecidableEq, Repr

namespace ProForm.OntologicalCategory

/-- The word class a category gives a proform by default: a pronoun where it stands for a person
or a thing, a determiner where it stands for a property or selects among the referents of a noun, and an adverb where it
stands for a place, a time, a manner or a reason. -/
def upos : OntologicalCategory → UD.UPOS
  | .person | .thing | .amount => .PRON
  | .property | .determiner => .DET
  | .place | .time | .manner | .reason => .ADV

end ProForm.OntologicalCategory

/-- A proform is a `Pronoun` with the ontological category it stands for and its word class,
which is the one its category fixes unless the entry says otherwise. -/
@[ext]
structure ProForm extends Pronoun where
  /-- The ontological category the form stands for, its general term. -/
  ontology : ProForm.OntologicalCategory
  /-- The word class, a pronoun, a determiner or an adverb. -/
  cat : UD.UPOS := ontology.upos

instance : DecidableEq ProForm := fun _ _ ↦ decidable_of_iff _ ProForm.ext_iff.symm

namespace ProForm

variable (p : ProForm)

/-- The token of a proform has its word class and the pronoun type `t` of its function. -/
def toWord (t : UD.PronType) : Morphology.Word := p.toPronoun.toWord (some t) (cat := p.cat)

/-- The token of an operator, a wh-phrase or a quantifier expression, is an R-expression where
its word class is nominal, as *who* and *someone* are and *where* is not, and is not a
pronominal. -/
theorem bindingClassOf_toWord {t : UD.PronType} (ht : Binding.IsOperator t) :
    Binding.bindingClassOf (p.toWord t) =
      if Binding.IsNominal p.cat then some .rExpression else none :=
  p.toPronoun.bindingClassOf_toWord_of_isOperator ht _

end ProForm
