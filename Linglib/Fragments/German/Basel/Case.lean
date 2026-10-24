module

public import Linglib.Fragments.German.Determiners

/-!
# Basel German case

This file defines the three cases of Basel German, nominative, accusative and dative, with the
forms of the definite article and of the stressed first person singular pronoun, following
Suter's grammar. The personal pronouns keep all three cases apart (§124). The article marks the
dative, but it never tells the accusative from the nominative, so that the accusative differs
from the nominative on nouns only by position in the clause (§82). The genitive has long vanished
as a case (§91), and the possessor is a dative, with a possessive pronoun or after *vo* (§193).

## Main declarations

* `German.Basel.Case`: the three cases.
* `German.Basel.article`, `German.Basel.pronoun`: the forms of the definite article in each gender
  and number (§83), and of the stressed first person singular pronoun (§125).
* `article_nom_eq_acc`, `article_dat_ne_nom`, `pronoun_injective`: the article marks the dative
  but not the accusative, and the pronoun marks both.

## Implementation notes

A cell holds all the forms Suter gives for it: the article *d* beside its full form *die*, and
the stressed *yy* beside *yych*. The genitive article *s* of names for a whole family,
*s Waagners* 'the Wagner family' (§83), and the forms *am* and *im* heard beside the dative *em*
(§85) are left out.

## References

* [suter-1992]
-/

@[expose] public section

namespace German.Basel

/-- The three cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The dative. -/
  | dat
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | dat => .dat

/-- The forms of the definite article (§83): *der* in the masculine and *s* in the neuter
nominative and accusative singular, *d* or *die* in the feminine singular and the plural, *em*
in the masculine and neuter dative singular, *der* in the feminine and *de* in the plural. -/
def article : GenderNumber → Case → Finset String
  | .sg .masc, .nom | .sg .masc, .acc => {"der"}
  | .sg .fem, .nom | .sg .fem, .acc | .pl, .nom | .pl, .acc => {"d", "die"}
  | .sg .neut, .nom | .sg .neut, .acc => {"s"}
  | .sg .masc, .dat | .sg .neut, .dat => {"em"}
  | .sg .fem, .dat => {"der"}
  | .pl, .dat => {"de"}

/-- The stressed first person singular pronoun (§125): *yych* or *yy*, *mii*, *miir*. -/
def pronoun : Case → Finset String
  | .nom => {"yych", "yy"}
  | .acc => {"mii"}
  | .dat => {"miir"}

/-- No form of the article tells the accusative from the nominative (§§82–83). -/
theorem article_nom_eq_acc (x : GenderNumber) : article x .nom = article x .acc := by
  revert x; decide

/-- The article tells the dative from the nominative in every gender and number (§83). -/
theorem article_dat_ne_nom (x : GenderNumber) : article x .dat ≠ article x .nom := by
  revert x; decide

/-- The pronoun keeps the three cases apart (§124), and so it is the pronoun that establishes
the accusative. -/
theorem pronoun_injective : Function.Injective pronoun := by
  decide

end German.Basel
