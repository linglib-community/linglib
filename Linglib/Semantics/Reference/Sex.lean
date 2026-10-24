module

public import Mathlib.Tactic.DeriveFintype

/-!
# Sex

The sex of a referent, the property sex-based gender assignment reads. A language's semantic
rules assign male and female humans, and the animals it sex-differentiates, to its genders by
it, and a noun restricts its referents to a sex when the language distinguishes a form for
males and another for females, Corbett's sex-differentiable nouns. Pronoun presuppositions read
it as the sex a referent is socially assigned.

## References

* [corbett-1991] — sex-differentiable nouns, chapter 3
* [corbett-fedden-2016]
-/

@[expose] public section

/-- The sex of a referent. -/
inductive Sex where
  | male
  | female
  deriving DecidableEq, Repr, Fintype
