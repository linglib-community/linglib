module

public import Linglib.Syntax.Category.Adjective.Basic
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Clause-embedding adjectives

Adjectives that take clausal complements: *annoyed (that p)*, *sorry (that p)*, *aware (that p)*,
*able (to VP)*. `ClauseEmbeddingAdjective` extends the `Adjective` core with
`Clause.Embedding`, what a predicate of any word class does with a clausal complement, and with its
valency, the diatheses of its complement with their controllers.

Whether an adjectival predicate takes a copula is a property of the language, not of the
adjective ([stassen-2013b]): English realizes these predicates as *be* and the adjective,
`ClauseEmbeddingAdjective.toVerb` with the copula *be*, while Mandarin encodes predicative
adjectives as verbs.

## References

* [stassen-2013b]
-/

@[expose] public section

/-- A clause-embedding adjective is the `Adjective` core with `Clause.Embedding`, and no verbal
morphology. -/
structure ClauseEmbeddingAdjective extends Adjective, Clause.Embedding where
  /-- The participants and the diatheses of the adjective's complement, the basic diathesis
  first. -/
  valency : Verb.Valency := .ofFrame .finiteClause
  deriving Repr, BEq

namespace ClauseEmbeddingAdjective

/-- The verb an adjective forms with a copula, the copula's form before the adjective's and the
adjective's `Clause.Embedding` carried over. -/
def toVerb (a : ClauseEmbeddingAdjective) (copula : String) : Verb :=
  { a.toEmbedding with
    morphs := [.free copula, .root a.form]
    valency := a.valency }

end ClauseEmbeddingAdjective
