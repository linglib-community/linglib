/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph

/-!
# Additive focus particles

An additive focus particle is a particle meaning 'also, too' that goes with a focused phrase, as
Japanese *mo* does in *Mary mo genki desu* 'Also Mary is well'. It stands before its phrase, as
English *also* does, or after it, as English *too* and Japanese *mo* do. Such particles often also
mean 'and' or 'even', and on an interrogative pronoun they form indefinites, Japanese *nani-mo*
'nothing'. In Haspelmath's account of coordination a construction with an additive focus
particle, 'A, also B' or 'A, B too', is one of the two main diachronic sources of conjunction, and
the coordinator that results stands by the second coordinand on the particle's side.

## Main definitions

* `AdditiveParticle`: the form of an additive focus particle and the side of its phrase on which
  it stands.

## Implementation notes

* The record holds no denotation. In one family of accounts the particle presupposes that an
  alternative to its phrase satisfies the predicate; Mitrović and Sauerland take the additive
  inference to be an implicature of a conjunction head.
* The side is stored for a clitic too, whose morph already has it.

## References

* [haspelmath-1997]
* [haspelmath-2007]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

/-- An additive focus particle of a language, meaning 'also, too'. -/
structure AdditiveParticle where
  /-- The form, a free word or a clitic. -/
  morph : Morphology.Morph
  /-- The side of the phrase it adds on which the particle stands. -/
  side : Morphology.Morph.Side
  deriving DecidableEq, Repr
