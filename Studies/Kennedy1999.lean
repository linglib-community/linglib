module

public import Linglib.Data.Examples.Kennedy1999
public import Mathlib.Order.Interval.Set.Basic

/-!
# Kennedy (1999): Projecting the Adjective

Kennedy argues that gradable adjectives denote measure functions from objects to extents on a
scale. The positive extent of an object, (30), runs from the bottom of the scale up to its
measure, and the negative extent, (31), from its measure to the top, so the antonymy
biconditional (54) follows from the complementarity of the two. Positive and negative extents are
disjoint sorts, so a comparison between them is undefined, which explains cross-polar anomaly
alongside incommensurability (section 3.1.7).

## Main results

* `Kennedy1999.antonymy_biconditional`: (54), *a is taller than b* iff *b is shorter than a*, on
  the extents of (30) and (31).
* `Kennedy1999.comparison_defined_iff`: a subdeletion comparative is acceptable exactly when the
  compared extents are of one sort on a shared scale, against the rows of sections 3.1.3–3.1.7.
* `Kennedy1999.measurePhrase_positive_iff`: an absolute measure phrase composes exactly with a
  positive adjective, sections 3.1.8–3.1.9.

## Implementation notes

Extents are the rays `Set.Iic (μ a)` and `Set.Ici (μ a)`, closed at the measure as in (30) and
(31). The embedding of measure functions into Klein's degree-free semantics is
`Degree.Delineation.ofMeasure`, whose ordering is degree comparison
(`Degree.Delineation.outranks_ofMeasure_iff`).

## References

* [kennedy-1999]
* [klein-1980]
-/

@[expose] public section

namespace Kennedy1999


/-! ### The algebra of extents (section 3.1.5) -/

section Extents

variable {E D : Type*} [LinearOrder D] (μ : E → D) (a b : E)

/-- The positive extent of `a`, (30), properly contains that of `b` exactly when the negative extent
of `b`, (31), properly contains that of `a`, the antonymy biconditional (54). -/
theorem antonymy_biconditional :
    Set.Iic (μ b) ⊂ Set.Iic (μ a) ↔ Set.Ici (μ a) ⊂ Set.Ici (μ b) :=
  Set.Iic_ssubset_Iic.trans Set.Ici_ssubset_Ici.symm

end Extents

/-! ### Cross-polar anomaly (Sections 3.1.3–3.1.7) -/

/-- The two compared adjectives have the same scale polarity. -/
def samePolarity (e : Datum) : Prop :=
  e.feature? "matrix_polarity" = e.feature? "standard_polarity"

instance (e : Datum) : Decidable (samePolarity e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The two compared adjectives project onto a shared scale. -/
def sharedScale (e : Datum) : Prop :=
  e.feature? "shared_scale" = some "true"

instance (e : Datum) : Decidable (sharedScale e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The subdeletion comparatives are the cross-polar anomalies, the same-polarity controls, the
ficus quadruple, and the incommensurability cases. -/
def crossPolarRows : List Datum :=
  [ Examples.cpa_long_short, Examples.cpa_short_long
  , Examples.subdel_pos_pos, Examples.subdel_neg_neg
  , Examples.ficus_tall_high, Examples.ficus_tall_low
  , Examples.ficus_short_low, Examples.ficus_short_high
  , Examples.incomm_tall_clever, Examples.incomm_tragic_heavy ]

/-- A subdeletion comparative is acceptable exactly when the compared extents are of the same
sort on a shared scale, which covers cross-polar anomaly and incommensurability at once. -/
theorem comparison_defined_iff :
    ∀ e ∈ crossPolarRows, e.judgment = .acceptable ↔ (samePolarity e ∧ sharedScale e) := by
  decide

/-! ### Measure phrases (Sections 3.1.8–3.1.9)

Measure phrases denote bounded extents. On a scale with a minimum the positive extents are
bounded and the negative ones are not, so an absolute construction composing a measure phrase
with a negative adjective is undefined, (69) *My Cadillac is 8 feet long* against (70) *My Fiat
is 5 feet short*; the phrasal comparative (73) *My Fiat is shorter than 8 feet* is the contrast,
its standard derived by applying the adjective to the measure phrase. -/

/-- The absolute measure-phrase constructions. -/
def measurePhraseAbsoluteRows : List Datum :=
  [ Examples.mp_cadillac, Examples.mp_fiat, Examples.mp_reich, Examples.mp_slow ]

/-- An absolute measure-phrase construction is acceptable exactly with a positive adjective,
whose extents are bounded. -/
theorem measurePhrase_positive_iff :
    ∀ e ∈ measurePhraseAbsoluteRows,
      e.judgment = .acceptable ↔ e.feature? "polarity" = some "positive" := by
  decide

end Kennedy1999
