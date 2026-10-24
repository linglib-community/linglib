module

public import Mathlib.Tactic.DeriveFintype

/-!
# Italian gender

Italian has two genders, the masculine and the feminine.

## References

* [corbett-1991]
-/

@[expose] public section

namespace Italian.Gender

/-- The two genders. -/
inductive Value where
  | masculine
  | feminine
  deriving DecidableEq, Repr, Fintype

end Italian.Gender
