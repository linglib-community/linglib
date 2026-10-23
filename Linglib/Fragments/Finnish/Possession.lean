module

public import Linglib.Fragments.Finnish.Phonology
public import Linglib.Syntax.Agreement.Paradigm

/-!
# Finnish possessive endings

A possessed Finnish noun takes a possessive ending that agrees in person and number with the
possessor, as in *talo-ni* 'my house', and the genitive of a personal pronoun may accompany
it, as in *minu-n talo-ni*. The endings are -ni, -si and -nsA in the singular and -mme, -nne
and -nsA in the plural, so that the third person alone does not distinguish number.

A possessive ending follows the case ending, and its form after one, and the case ending's
before it, are in `Finnish.Nominal`.

## Main definitions

* `Finnish.Possession.endings`: the possessive endings, an agreement paradigm.

## Main results

* `Finnish.Possession.realize_eq_realize_iff`: two cells share an ending exactly when they are
  the same cell or both are third person.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish.Possession

open Phonology Agreement

/-- The possessive endings. -/
def endings : Paradigm (List Segment) :=
  [(.personNumber .first .singular, [n, i]), (.personNumber .second .singular, [s, i]),
    (.personNumber .third .singular, [n, s, A]), (.personNumber .first .plural, [m, m, e]),
    (.personNumber .second .plural, [n, n, e]), (.personNumber .third .plural, [n, s, A])]

/-- Two cells share an ending exactly when they are the same cell or both are third
person. -/
theorem realize_eq_realize_iff :
    ∀ p ∈ Bundle.personNumberCells, ∀ q ∈ Bundle.personNumberCells,
      endings.realize p = endings.realize q ↔ p = q ∨ p.person = .third ∧ q.person = .third := by
  decide

end Finnish.Possession
