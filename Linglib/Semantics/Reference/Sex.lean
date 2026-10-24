module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.Features

/-!
# Sex

The sex of a referent, the property sex-based gender assignment reads. A language's semantic
rules assign male and female humans, and the animals it sex-differentiates, to its genders by
it, and a noun restricts its referents to a sex when the language distinguishes a form for
males and another for females, Corbett's sex-differentiable nouns. A word token realizes it as a
Universal Dependencies gender tag (`Sex.toUD`).

## References

* [corbett-1991] — sex-differentiable nouns, §3.1.1, p. 34
* [corbett-fedden-2016]
-/

@[expose] public section

/-- The sex of a referent. -/
inductive Sex where
  | male
  | female
  deriving DecidableEq, Repr, Fintype

/-- A sex realizes as the masculine or the feminine tag. -/
def Sex.toUD : Sex → UD.Gender
  | .male => .Masc
  | .female => .Fem
