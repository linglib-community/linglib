module

public import Mathlib.Tactic.DeriveFintype

/-!
# Property-concept classes

Dixon's seven semantic types of property concept, the meanings that make up the English
adjective class. Across languages the words of a type may be adjectives, verbs or nouns: in
Dixon's survey dimension, age, value and colour are likely to be adjectives however small the
adjective class, while a language whose adjective class is closed typically makes its physical
properties verbs and its human propensities nouns.

## Main declarations

* `PropertyConcept.Class`: Dixon's seven types.

## References

* [dixon-1982]
-/

@[expose] public section

namespace Semantics

/-- [dixon-1982]'s seven semantic types of property concept, with his English examples (p. 16).
He sets aside position (*high*, *low*, *near*, *far*), which most languages express by adverbs
(fn. 11). -/
inductive PropertyConcept.Class where
  /-- *big*, *large*, *little*, *small*, *long*, *short*, *wide*, *narrow*, *thick*, *fat*,
  *thin*. -/
  | dimension
  /-- *hard*, *soft*, *heavy*, *light*, *rough*, *smooth*, *hot*, *cold*, *sweet*, *sour*. -/
  | physicalProperty
  /-- *black*, *white*, *red*. -/
  | color
  /-- *jealous*, *happy*, *kind*, *clever*, *generous*, *cruel*, *rude*, *proud*, *wicked*. -/
  | humanPropensity
  /-- *new*, *young*, *old*. -/
  | age
  /-- *good*, *bad*, *proper*, *perfect*, and hyponyms of *good* and *bad* such as *excellent*,
  *delicious* and *atrocious*. -/
  | value
  /-- *fast*, *quick*, *slow*. -/
  | speed
  deriving DecidableEq, Fintype, Repr

end Semantics
