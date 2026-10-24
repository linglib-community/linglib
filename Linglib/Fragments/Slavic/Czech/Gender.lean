module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Gender.Basic

/-!
# Czech noun gender

This file defines the controller genders of Czech. Short counts three genders, "the
subcategory of animacy functioning within the masculine only" (p. 465), and agreement treats
the masculine animate and the masculine inanimate as two classes: "Agreement with mixed-gender
noun phrases (for past tenses and conditional) is dominated in turn by any masculine–animate,
masculine–inanimate and feminine" (p. 503), so that *Pes a kočka seděli na rohožce* 'The dog and
the cat were sitting on the mat' takes the masculine animate plural and *Dům i stáda byly
zničeny* 'The house and flocks were destroyed' the masculine inanimate plural. The controller
genders are therefore four, and the comparative labels merge the two masculines.

## Main definitions

* `Czech.Gender.Value`: the four controller genders
* `Czech.Gender.Value.toLabel`: their comparative labels
* `Czech.Gender.Value.IsAnimate`: the masculine animate

## References

* [short-1993-czech]
-/

@[expose] public section

namespace Czech.Gender

/-- The controller genders are the masculine animate, the masculine inanimate, the feminine and
the neuter, animacy being a subcategory of the masculine alone. -/
inductive Value where
  | mascAnimate
  | mascInanimate
  | feminine
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender, both masculines being masculine. -/
def Value.toLabel : Value → Gender.Label
  | .mascAnimate | .mascInanimate => .masculine
  | .feminine => .feminine
  | .neuter => .neuter

/-- A gender is animate when it is the masculine animate. -/
def Value.IsAnimate (g : Value) : Prop := g = .mascAnimate

instance : DecidablePred Value.IsAnimate := fun g ↦ inferInstanceAs (Decidable (g = _))

end Czech.Gender
