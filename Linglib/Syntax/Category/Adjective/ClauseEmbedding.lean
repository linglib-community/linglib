module

public import Linglib.Syntax.Category.Adjective.Basic
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Clause-embedding adjectives

Adjectives that take clausal complements: *annoyed (that p)*, *sorry (that p)*, *aware (that p)*,
*able (to VP)*. As `GradableAdjective` in `Semantics/Degree/Adjective.lean` extends the
`Adjective` core with its degree semantics, `ClauseEmbeddingAdjective` extends it with the
clausal-selection facets of a verb entry: its valency, the diatheses of its complement with
their controllers, and its presupposition, implicative and attitude profiles.

Whether an adjectival predicate takes a copula is a property of the language, not of the
adjective ([stassen-2013b]): English realizes these predicates as *be* and the adjective,
`ClauseEmbeddingAdjective.toVerb` with the copula *be*, while Mandarin encodes predicative
adjectives as verbs.

## References

* [stassen-2013b]
-/

@[expose] public section

/-- A clause-embedding adjective is the `Adjective` core with the clausal-selection facets it
shares with clause-embedding verbs, and no verbal morphology. -/
structure ClauseEmbeddingAdjective extends Adjective, Verb.Presupposition, Verb.Attitude where
  /-- The participants and the diatheses of the adjective's complement, the basic diathesis
  first. -/
  valency : Verb.Valency := .ofFrame .finiteClause
  deriving Repr, BEq

namespace ClauseEmbeddingAdjective

/-- The verb an adjective forms with a copula, the copula's form before the adjective's and the
adjective's clausal-selection facets carried over. -/
def toVerb (a : ClauseEmbeddingAdjective) (copula : String) : Verb :=
  { a.toPresupposition, a.toAttitude with
    morphs := [.free copula, .root a.form]
    valency := a.valency }

end ClauseEmbeddingAdjective
