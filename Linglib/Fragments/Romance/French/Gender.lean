module

public import Mathlib.Tactic.DeriveFintype

/-!
# French gender

French has two genders, the masculine and the feminine.

## References

* [corbett-1991]
-/

@[expose] public section

namespace French.Gender

/-- The two genders. -/
inductive Value where
  | masculine
  | feminine
  deriving DecidableEq, Repr, Fintype

end French.Gender
