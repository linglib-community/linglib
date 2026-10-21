module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Nominality

The nominality of a nominal ranks personal pronouns above proper names above common nouns. It is
the top of Aissen's definiteness scale, where pronouns and names are the high end of the
definites, and Haspelmath's scale of nominal types; its cut between pronouns and nouns is the
opposition of person forms to full nominals and the pronoun–noun division of Corbett's animacy
hierarchy.

## References

* [aissen-2003]
* [corbett-2000]
* [haspelmath-2021]
-/

@[expose] public section

/-- The nominality of a nominal ranks a personal pronoun above a proper name above a common
noun. -/
inductive Nominality where
  | commonNoun
  | properName
  /-- A personal pronoun. -/
  | pronoun
  deriving DecidableEq, Repr, Fintype

namespace Nominality

/-- The rank on the scale, 0 for a common noun, 1 for a proper name and 2 for a pronoun. -/
def rank : Nominality → ℕ
  | .commonNoun => 0
  | .properName => 1
  | .pronoun => 2

instance : LinearOrder Nominality := LinearOrder.lift' rank (by decide)

end Nominality

