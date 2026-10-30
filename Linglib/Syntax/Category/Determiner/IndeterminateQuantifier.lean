module

public import Linglib.Syntax.Category.Classifier.Basic
public import Linglib.Syntax.Category.Coordinator
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Indeterminate quantifiers

An indeterminate quantifier is built from an indeterminate pronoun, an interrogative, and a
particle that is also a coordinator of the language. Japanese *dare-ka* 'someone' and *dare-mo*
'everyone' combine *dare* 'who' with *ka* 'or' and *mo* 'and', and Latin *quisque* 'each'
combines *quis* 'who' with the enclitic *-que* 'and'. A coordinator has a quantifier use when an
indeterminate quantifier of its language has it as its particle. What the quantifier denotes is
`IndeterminateQuantifier.reading`, in `Semantics/Quantification/IndeterminateQuantifier.lean`.

## Main definitions

* `IndeterminateQuantifier`: an indeterminate and a particle, with the classifier between them
  where there is one.
* `IndeterminateQuantifier.form`, `IndeterminateQuantifier.toQuantifier`: its citation form and
  its determiner record.

## References

* [kratzer-shimoyama-2002]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

/-- An indeterminate quantifier is an indeterminate pronoun with a particle that is a coordinator
of the language, and the classifier between them where there is one. -/
structure IndeterminateQuantifier where
  /-- The indeterminate pronoun. -/
  indeterminate : InterrogativePronoun
  /-- The particle, a coordinator of the language. -/
  particle : Coordinator
  /-- The classifier after the indeterminate, as in Japanese *nan-nin-ka*. -/
  classifier : Option Classifier := none
  deriving DecidableEq

namespace IndeterminateQuantifier

variable (q : IndeterminateQuantifier)

/-- The citation form joins the indeterminate, its classifier and the particle by hyphens, and
puts the particle of a determiner, such as Japanese *dono* 'which', after the noun the
determiner takes. -/
def form : String :=
  let p := q.particle.morph.form
  if q.indeterminate.ontology = .determiner then q.indeterminate.form ++ " … " ++ p
  else q.indeterminate.form ++ (q.classifier.elim "" ("-" ++ ·.form)) ++ "-" ++ p

/-- An indeterminate quantifier's determiner record carries its form. -/
def toQuantifier : QuantificationalDeterminer := { form := q.form }

end IndeterminateQuantifier
