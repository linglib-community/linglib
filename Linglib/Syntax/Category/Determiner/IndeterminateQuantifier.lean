/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Classifier
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Indeterminate quantifiers

An indeterminate quantifier is built from an indeterminate pronoun, a proform that is an
interrogative in a question, and a particle. Japanese *dare-ka* 'someone' and *dare-mo*
'everyone' combine *dare* 'who' with *ka* and *mo*, and Latin *quisque* 'each' combines *quis*
'who' with the enclitic *-que*. The particle often has the form of a coordinator or of an
additive focus particle of the language, as *ka* 'or', *mo* 'and, also' and *-que* 'and' do.

## Main definitions

* `IndeterminateQuantifier`: an indeterminate and a particle, with the classifier between them
  where there is one, and the readings of the whole.
* `IndeterminateQuantifier.form`, `IndeterminateQuantifier.toQuantifier`,
  `IndeterminateQuantifier.toIndefinite`: its citation form, its determiner record and the
  indefinite pronoun it is.

## Implementation notes

The particle is a morph, and the readings are those of the quantifier as a whole. Accounts differ
on what the particle is. For Kratzer and Shimoyama it is the quantifier over the alternatives the
indeterminate introduces. Shimoyama keeps the universal *mo* apart from the additive and
conjunctive *mo*, and Haspelmath takes the identity of form with 'and' and 'or' to be largely
accidental. Mitrović and Sauerland take one morpheme to conjoin, quantify and add, and for
Szabolcsi one particle occurs in all these contexts without itself denoting meet or join. Each
account is stated in its own study over the same entries.

## References

* [haspelmath-1997]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
* [szabolcsi-2015]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

/-- An indeterminate quantifier is an indeterminate pronoun with a particle, and the classifier
between them where there is one. -/
structure IndeterminateQuantifier where
  /-- The indeterminate pronoun. -/
  indeterminate : ProForm
  /-- The particle. -/
  particle : Morphology.Morph
  /-- The classifier after the indeterminate, as in Japanese *nan-nin-ka*. -/
  classifier : Option Classifier := none
  /-- The readings of the quantifier, empty when its standard is left to context. -/
  readings : Finset Quantifier.Det.Symbol := ∅
  deriving DecidableEq

namespace IndeterminateQuantifier

variable (q : IndeterminateQuantifier)

/-- The citation form joins the indeterminate, its classifier and the particle by hyphens, and
puts the particle of a determiner, such as Japanese *dono* 'which', after the noun the
determiner takes. -/
def form : String :=
  let p := q.particle.form
  if q.indeterminate.cat = .DET then q.indeterminate.form ++ " … " ++ p
  else q.indeterminate.form ++ (q.classifier.elim "" ("-" ++ ·.form)) ++ "-" ++ p

/-- The indefinite pronoun an indeterminate quantifier is: its indeterminate's features, category
and word class under its citation form. -/
def toIndefinite : IndefinitePronoun := .ofProForm (fun _ ↦ q.form) q.indeterminate

/-- An indeterminate quantifier's determiner record carries its form and its readings. -/
def toQuantifier : QuantificationalDeterminer := { form := q.form, readings := q.readings }

end IndeterminateQuantifier
