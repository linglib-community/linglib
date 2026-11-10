module

public import Linglib.Semantics.Negation.AntonymForm

/-!
# The division of pragmatic labour between negated antonyms

A simple form and the negated form of the other pole, *happy* and *not unhappy*, share their
literal meaning when the poles are contradictory, and the negated form extends it when they are
contrary. Horn's division of pragmatic labour gives the simple form the stereotypical uses and the
negated form [the rest](##AntonymForm.disjoint_dividedUse_flip), which is the middle ground of a
contrary pair and, on Krifka's account of a contradictory one, the mild cases that the simple form
is not safely used for. [Without a stereotype narrower than the literal meaning, a contradictory
pair leaves the negated forms nothing](##AntonymForm.dividedUse_smul_self).

## References

* [horn-1984]
* [horn-1989]
* [levinson-2000]
* [krifka-2007b]
-/

@[expose] public section

namespace AntonymForm

variable {D : Type*}

/-- The division of pragmatic labour between a simple form and the negated form of the other
pole, which shares its literal meaning or extends it: the simple form is restricted to the
stereotypical uses `core` of its pole, and the negated form to what its literal meaning has
outside the stereotypical uses of the other pole. [horn-1984] states the division, and
[krifka-2007b] derives it for the M principle by avoidance of synonymy. -/
def dividedUse (ext core : Polarity → Set D) (f : AntonymForm) : Set D :=
  match f.polarity with
  | .positive => core f.pole
  | .negative => denotation ext f \ core (.negative * f.pole)

/-- A negated form is not used where the simple form of the other pole is. -/
theorem disjoint_dividedUse_flip (ext core : Polarity → Set D) (p : Polarity) :
    Disjoint (dividedUse ext core ⟨p, .negative⟩)
      (dividedUse ext core ⟨.negative * p, .positive⟩) :=
  Set.disjoint_sdiff_left

/-- With nothing stereotypical beyond the literal meaning, contradictory poles leave the negated
forms no use: the division needs the simple forms restricted. -/
theorem dividedUse_smul_self (U : Set D) (p : Polarity) :
    dividedUse (· • U) (· • U) ⟨p, .negative⟩ = ∅ := by
  show Polarity.negative • p • U \ (Polarity.negative * p) • U = ∅
  rw [mul_smul, sdiff_self]
  rfl

end AntonymForm
