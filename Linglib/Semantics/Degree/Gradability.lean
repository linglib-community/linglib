module

public import Linglib.Semantics.Degree.ScalarDimension
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Comparison

/-!
# Gradability

`Gradability` is the degree semantics of a gradable predicate of any category: the dimension it
measures, the pole it measures towards, and any lexically fixed standard. The scale and the positive
standard are derived from these, the standard by Interpretive Economy unless the lexicon fixes it,
so that *wet* and the verb *believe* get theirs by one definition. Two poles of one dimension [take
contradictory standards exactly when its scale has one
endpoint](##Gradability.complementary_standard_iff).

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
-/

@[expose] public section

/-- A directed scale is a comparison scale with a polarity. [cresswell-1976] reads it as a relation
ordering degrees upward or, for *short*, downward; for [kennedy-1999] it is the ordered set of the
positive or the negative extents on the scale. Comparison is defined only within one. -/
abbrev DirectedScale := ComparisonScale × Polarity

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

/-- The directed scale of a gradable predicate is its comparison scale with its polarity. -/
def directedScale : DirectedScale := (g.dimension.comparisonScale, g.polarity)

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

/-- Two poles of one dimension without lexical standards take complementary standards, so that
they are contradictory, exactly when the dimension's scale has one endpoint. -/
theorem complementary_standard_iff {g h : Gradability} (hd : g.dimension = h.dimension)
    (hg : g.polarity = .positive) (hh : h.polarity = .negative)
    (hgl : g.lexicalStandard = none) (hhl : h.lexicalStandard = none) :
    g.standard.Complementary h.standard ↔
      g.dimension.boundedness = .lowerClosed ∨ g.dimension.boundedness = .upperClosed := by
  rw [standard_of_lexicalStandard_eq_none hgl, standard_of_lexicalStandard_eq_none hhl,
    boundedness, boundedness, hg, hh, ← hd, Boundedness.negative_smul]
  exact Boundedness.complementary_defaultStandard_dual_iff

end Gradability
