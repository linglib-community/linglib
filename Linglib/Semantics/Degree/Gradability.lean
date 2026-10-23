module

public import Linglib.Semantics.Degree.Scale
public import Linglib.Semantics.Degree.Antonymy

/-!
# Gradability

This file defines `Degree.Gradability`, the degree semantics of a gradable predicate of any
category: the dimension it measures, the pole it measures towards, and any lexically fixed
standard. The scale and the positive standard are derived from these, the standard by Interpretive
Economy unless the lexicon fixes it, so that *wet* and the verb *believe* get theirs by one
definition. Adjectives and verbs project their entries onto it.

## Main definitions

* `Gradability`: a dimension, a polarity and an optional lexical standard.
* `Gradability.boundedness`: the scale, the dimension's dualized at the negative pole.
* `Gradability.standard`: the lexical standard, or the scale's default.

## Main statements

* `Gradability.complementary_standard_iff`: two poles of one dimension take contradictory standards
  exactly when its scale has one endpoint.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
-/

@[expose] public section

namespace Degree

/-- The degree semantics of a gradable predicate is the dimension it measures, the pole it
measures towards, and the standard its lexicon fixes, `none` taking the scale's default. -/
structure Gradability where
  /-- The dimension measured. -/
  dimension : ScalarDimension
  /-- The pole measured towards, negative for the negative member of an antonym pair. -/
  polarity : Polarity := .positive
  /-- The lexically fixed positive standard, `none` taking the scale's default. -/
  lexicalStandard : Option PositiveStandard := none
  deriving DecidableEq, Repr

namespace Gradability

variable (g : Gradability)

/-- The scale is the dimension's, dualized at the negative pole. -/
def boundedness : Boundedness := g.polarity • g.dimension.boundedness

/-- The positive standard is the lexical one if any, and otherwise the one Interpretive Economy
prefers on the scale. -/
def standard : PositiveStandard := g.lexicalStandard.getD g.boundedness.defaultStandard

variable {g}

theorem standard_of_lexicalStandard_eq_none (h : g.lexicalStandard = none) :
    g.standard = g.boundedness.defaultStandard := by
  simp [standard, h]

theorem admits_standard (h : g.lexicalStandard = none) : g.boundedness.Admits g.standard :=
  standard_of_lexicalStandard_eq_none h ▸ Boundedness.admits_defaultStandard _

theorem complementary_standard_iff {g h : Gradability} (hd : g.dimension = h.dimension)
    (hg : g.polarity = .positive) (hh : h.polarity = .negative)
    (hgl : g.lexicalStandard = none) (hhl : h.lexicalStandard = none) :
    g.standard.Complementary h.standard ↔
      g.dimension.boundedness = .lowerClosed ∨ g.dimension.boundedness = .upperClosed := by
  rw [standard_of_lexicalStandard_eq_none hgl, standard_of_lexicalStandard_eq_none hhl,
    boundedness, boundedness, hg, hh, ← hd, Boundedness.negative_smul]
  exact Boundedness.complementary_defaultStandard_dual_iff

end Gradability

end Degree
