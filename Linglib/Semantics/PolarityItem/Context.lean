/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# The contexts of a polarity item

A *licensing context* is a construction in which a grammar says that a polarity item occurs or
fails to occur: under clausal negation, in the scope of *nobody* or *few*, in the antecedent of a
conditional, in a polar question, in a plain positive assertion. The constructions are names. The
operator that a construction places over the item and the function of Haspelmath's map that it
realizes are given in `Semantics/PolarityItem/LicensingContext.lean`.

## Implementation notes

* A question that contains a negation is not a question context, since the negation is the
  operator over the item there. The two question contexts are the questions without one.
* The inventory consists of the constructions to which the library gives a semantics, together
  with the positive assertion. It is not an exhaustive list.

## References

* [ladusaw-1979]
* [zwarts-1998]
* [haspelmath-1997]
-/

@[expose] public section

namespace PolarityItem

/-- A construction in which a polarity item occurs or fails to occur. -/
inductive LicensingContext where
  /-- A positive assertion of an episodic sentence, with no operator over the item. -/
  | positiveAssertion
  /-- Clausal negation, as in *not*. -/
  | negation
  /-- A negative quantifier, as in *nobody*. -/
  | nobody
  /-- *Few* NP, in the proportional reading of the English language file, which lies below the
  stronger
  *no* on its scale. -/
  | few
  /-- *At most n* NP, which lies below the stronger *at most n − 1* on its scale. -/
  | atMost
  /-- The restrictor of a universal, as in *everyone who*. -/
  | universalRestrictor
  /-- The restrictor of a negative quantifier, as in *no one who*. -/
  | noRestrictor
  /-- A *without*-phrase, in which the matrix predicate holds without the predicate of the
  phrase. -/
  | withoutClause
  /-- A *before*-clause. -/
  | beforeClause
  /-- A clausal comparative, as in *taller than S*, which places the individual above every degree
  of the clause. -/
  | clausalComparative
  /-- *Too* ADJ *to* VP, which places the individual above every degree at which the infinitive
  holds. -/
  | tooTo
  /-- A verb of doubting, as in *I doubt that*, whose subject does not believe the complement. -/
  | doubtVerb
  /-- A verb of denying, as in *she denied that*, whose subject asserts the negation of the
  complement. -/
  | denyVerb
  /-- Negation over a neg-raising attitude in a superordinate clause, as in *I don't think that*.
  The attitude presupposes the excluded middle, so its negation is true where the attitude holds
  of the negated complement ([gajewski-2007]). -/
  | superordinateNegation
  /-- The scope of focus *only*. -/
  | onlyFocus
  /-- An adversative predicate, as in *sorry*, *surprised*, and *regret*. -/
  | adversative
  /-- A superlative, in its comparison class. -/
  | superlative
  /-- The antecedent of a conditional. -/
  | conditionalAntecedent
  /-- Temporal *since*, as in *it's been five years since*. -/
  | sinceTemporal
  /-- A polar question that contains no negation. -/
  | polarQuestion
  /-- A constituent question that contains no negation. -/
  | constituentQuestion
  /-- A possibility modal. -/
  | modalPossibility
  /-- A necessity modal. -/
  | modalNecessity
  /-- An imperative. -/
  | imperative
  /-- A generic sentence. -/
  | generic
  /-- A free relative, as in *whatever* and *whoever*. -/
  | freeRelative
  deriving DecidableEq, Fintype, Repr


end PolarityItem
