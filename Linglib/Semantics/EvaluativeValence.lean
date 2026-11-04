module

/-!
# Evaluative valence

`EvaluativeValence` records whether a predicate denotes a good, a bad or an evaluatively neutral
property, as *hope* and *wonderful* do against *fear* and *horrible*. It is a lexical property of
adjectives and attitude verbs alike, and it is distinct from scalar polarity, though
[the poles of an antonym pair exchange it](##EvaluativeValence.flip).

## References

* [nouwen-2024]
* [qing-uegaki-2025]
-/

@[expose] public section

/-- The evaluative valence of a gradable predicate records whether it denotes a good, a bad or
an evaluatively neutral property, which is distinct from scalar polarity ([nouwen-2024]).
Negative valence yields high-degree intensifiers and positive valence moderate-degree ones, which
Nouwen explains by the Goldilocks effect, the negative evaluation of a scale's extremes. -/
inductive EvaluativeValence where
  | positive
  | negative
  | neutral
  deriving Repr, DecidableEq

/-- The valence of the opposite pole of an antonym pair swaps positive and negative and keeps
neutral. -/
def EvaluativeValence.flip : EvaluativeValence → EvaluativeValence
  | .positive => .negative
  | .negative => .positive
  | .neutral => .neutral
