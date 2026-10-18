module

public import Linglib.Morphology.Morph

/-!
# Additive particles

An additive particle is a focus particle meaning 'also, too', English *too* in *Mary is well too*.
Such particles often also mean 'and': Japanese *mo* is 'too' after one phrase and 'and' after each
of two conjuncts, and Haspelmath counts the additive particle among the two main sources of
conjunction. This file defines the lexical record of an additive particle; a coordinator whose form
is that of an additive particle is `Coordinator.IsAlsoAdditive`.

## Main definitions

* `AdditiveParticle`: the form and gloss of an additive particle.

## References

* [haspelmath-1997]
* [haspelmath-2007]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

/-- An additive particle of a language is a focus particle meaning 'also, too'. -/
structure AdditiveParticle where
  /-- The form, a free word or a clitic. -/
  morph : Morphology.Morph
  /-- The gloss. -/
  gloss : String
  deriving DecidableEq, Repr
