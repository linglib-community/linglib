module

public import Linglib.Syntax.Category.Classifier.Basic
public import Linglib.Syntax.Category.Coordinator
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Indeterminate quantifiers

An indeterminate quantifier is built from an indeterminate pronoun, a proform that is an
interrogative in a question, and a particle that is also a coordinator of the language.
Japanese *dare-ka* 'someone' and *dare-mo* 'everyone' combine *dare* 'who' with *ka* 'or' and
*mo* 'and', and Latin *quisque* 'each' combines *quis* 'who' with the enclitic *-que* 'and'. A coordinator has a quantifier use when an
indeterminate quantifier of its language has it as its particle. What the quantifier denotes is
`IndeterminateQuantifier.reading`, in `Semantics/Quantification/IndeterminateQuantifier.lean`.

## Main definitions

* `IndeterminateQuantifier`: an indeterminate and a particle, with the classifier between them
  where there is one.
* `IndeterminateQuantifier.form`, `IndeterminateQuantifier.toQuantifier`,
  `IndeterminateQuantifier.toIndefinite`: its citation form, its determiner record and the
  indefinite pronoun it is.

## References

* [kratzer-shimoyama-2002]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

/-- An indeterminate quantifier is an indeterminate pronoun with a particle that is a coordinator
of the language, and the classifier between them where there is one. -/
structure IndeterminateQuantifier where
  /-- The indeterminate pronoun. -/
  indeterminate : ProForm
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
  if q.indeterminate.cat = .DET then q.indeterminate.form ++ " … " ++ p
  else q.indeterminate.form ++ (q.classifier.elim "" ("-" ++ ·.form)) ++ "-" ++ p

/-- The indefinite pronoun an indeterminate quantifier is, a member of the series its particle
marks: its indeterminate's features, category and word class under its citation form. -/
def toIndefinite : IndefinitePronoun := .ofProForm (fun _ ↦ q.form) q.indeterminate

/-- An indeterminate quantifier's determiner record carries its form. -/
def toQuantifier : QuantificationalDeterminer := { form := q.form }

end IndeterminateQuantifier
