module

public import Mathlib.Basic.Real.Basic
public import Linglib.Semantics.Degree.Measure.Dimension

/-!
# Dimensioned measure functions

A measure function maps entities to magnitudes on a scale `D` in a dimension, such as mass or
volume, and a measure term names one: `⟦kilo⟧ = λn. λx. μ_kg(x) = n`. Scontras classifies the
nouns that turn substance terms into countable expressions.

## Main definitions

* `DimensionedMeasure`: a measure function tagged with its dimension.
* `QuantizingNounClass`: measure terms, container nouns and atomizers.

## References

* [scontras-2014]
* [zabbal-2005]
* [bipm-2019]
-/

@[expose] public section

namespace Degree

/-! ### Measure functions -/

/-- A measure function maps entities to magnitudes on the scale `D` in a dimension. Following
[scontras-2014], degrees are pairs ⟨μ, n⟩ of a measure function and a numerical value. μ_kg
measures mass and μ_L volume. The cardinality measure μ_card of [zabbal-2005]'s Num head card,
with which Scontras aligns measure terms, counts, so its values are numbers of entities, of
dimension `1` ([bipm-2019]). Non-negativity and additivity are properties of a measure, not
fields. -/
structure DimensionedMeasure (E : Type*) (D : Type := ℝ) where
  /-- The dimension the function measures in. -/
  dimension : QuantityDimension
  /-- The function sends an entity to its magnitude. -/
  toFun : E → D

variable {D : Type}

/-- A dimensioned measure coerces to its function. -/
instance {E : Type*} : CoeFun (DimensionedMeasure E D) (fun _ ↦ E → D) where
  coe μ := μ.toFun

/-! ### Quantizing nouns -/

/-- Quantizing nouns turn substance terms into countable expressions. [scontras-2014]
(Ch. 3) identifies three classes with Rothstein-style diagnostics (Table 3.5, p. 89).
Measure terms (kilo, liter) name a measure function directly and always license a MEASURE
reading. Container nouns (glass, box) are non-relational predicates with a CONTAINER reading by
default, ambiguous toward MEASURE when the container's volume can serve as a measure unit.
Atomizers (grain, drop, piece) are relational, partitioning nouns (eqs. (77), (87)) that impose a
partition into self-connected atoms via π, and they are counted by CARD over the partition, not
measured. -/
inductive QuantizingNounClass where
  /-- A measure term, such as *kilo*, *liter* or *meter*. -/
  | measureTerm
  /-- A container noun, such as *glass*, *box* or *cup*. -/
  | containerNoun
  /-- An atomizer, such as *grain*, *piece* or *drop*. -/
  | atomizer
  deriving Repr, DecidableEq

end Degree
