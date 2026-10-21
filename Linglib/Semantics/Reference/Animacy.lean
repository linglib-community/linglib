module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Animacy

The animacy of a referent places it on the scale human > animate > inanimate, the animacy
hierarchy proper. Corbett reads the wider hierarchies that govern number marking, which put the
personal pronouns above all nouns, as this scale combined with a person scale and the distinction
between pronouns and nouns, after Comrie; Aissen crosses it with definiteness to state
differential object marking.

## References

* [aissen-2003]
* [comrie-1989]
* [corbett-2000]
-/

@[expose] public section

/-- The animacy of a referent ranks the human above the non-human animate above the inanimate,
as on Aissen's animacy scale and Corbett's animacy hierarchy proper. -/
inductive Animacy where
  | inanimate
  /-- Non-human animates, Comrie's and Haspelmath's *animal*. -/
  | animate
  | human
  deriving DecidableEq, Repr, Fintype

namespace Animacy

/-- The rank on the scale, 0 for the inanimate, 1 for the animate and 2 for the human. -/
def rank : Animacy → ℕ
  | .inanimate => 0
  | .animate => 1
  | .human => 2

instance : LinearOrder Animacy := LinearOrder.lift' rank (by decide)

/-- The animacies, most animate first. -/
def all : List Animacy := [.human, .animate, .inanimate]

end Animacy

