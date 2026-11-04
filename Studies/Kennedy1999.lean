module

public import Linglib.Data.Examples.Kennedy1999
public import Linglib.Fragments.English.Adjectives
public import Linglib.Fragments.English.MeasurePhrases
public import Mathlib.Order.Interval.Set.Basic

/-!
# Kennedy (1999): Projecting the Adjective

Kennedy argues that gradable adjectives denote measure functions from objects to extents on a
scale. The positive extent of an object, (30), runs from the bottom of the scale up to its
measure, and the negative extent, (31), from its measure to the top, so the antonymy
biconditional (54) follows from the complementarity of the two. Points on a scale cannot tell the
two polarities apart, but extents can: [no proper extent is of both
sorts](##polarity_eq_of_extent_eq). A comparison is defined only within one ordered set, which
[decides every example](##comparison_defined_iff): incommensurable adjectives lie on different
scales, cross-polar ones on one scale in different sorts, and a negative adjective cannot take a
measure phrase because measure phrases name bounded extents and [only positive extents are
bounded](##bddAbove_extent_iff).

## Implementation notes

Extents are the rays `Set.Iic` and `Set.Ici`, closed at the measure as in (30) and (31). The
embedding of measure functions into Klein's degree-free semantics is
`Delineation.ofMeasure`, whose ordering is degree comparison
(`Delineation.outranks_ofMeasure_iff`). The scale and sort of an example are read from
`English.Adjectives` and `English.MeasurePhrases`: `ScalarDimension.comparisonScale` merges
*long*, *wide*, *tall* and *high* as "some notion of linear extent" (pp. 16-17).

## TODO

* The labels of the measure-phrase rows are the book's as first coded. The thesis numbers the same
  sentences (66), (67), (70), (76) and (77), three lower, and the book's chapter 3 was not at hand
  to check them.
* Comparison of deviation (section 3.2) and the positives that look like negatives (section 3.1.9).

## References

* [kennedy-1999]
* [klein-1980]
-/

@[expose] public section

namespace Kennedy1999


/-! ### The algebra of extents (section 3.1.5) -/

section Extents

variable {E D : Type*} [LinearOrder D] (μ : E → D) (a b : E)

/-- The positive extent of `a` (30) properly contains that of `b` iff the negative extent of `b`
(31) properly contains that of `a` (54). -/
theorem antonymy_biconditional :
    Set.Iic (μ b) ⊂ Set.Iic (μ a) ↔ Set.Ici (μ a) ⊂ Set.Ici (μ b) :=
  Set.Iic_ssubset_Iic.trans Set.Ici_ssubset_Ici.symm

end Extents

/-! ### Cross-polar anomaly and measure phrases (Sections 3.1.3–3.1.9)

Antonyms share a scale, so incommensurability alone cannot explain cross-polar anomaly (section
3.1.4). What separates them is that a positive and a negative extent are different objects, and
a relation holds only within one ordered set. -/

section Sorts

variable {D : Type*} [LinearOrder D] {p q : Polarity} {x y : D}

/-- The extent of polarity `p` at the measure `x`, (30) and (31). -/
def extent : Polarity → D → Set D
  | .positive, x => Set.Iic x
  | .negative, x => Set.Ici x

private theorem Iic_eq_univ_of_eq_Ici (h : Set.Iic x = Set.Ici y) : Set.Iic x = Set.univ :=
  have hyx : y ≤ x := h.ge (Set.self_mem_Ici)
  Set.eq_univ_of_forall fun z ↦ (le_total z x).elim id fun hxz ↦ h.ge (hyx.trans hxz)

/-- An extent determines its polarity unless it is the whole scale, which is not a proper extent
(28), (29): the positive and the negative extents are disjoint (p. 254). -/
theorem polarity_eq_of_extent_eq (hp : extent p x ≠ Set.univ) (h : extent p x = extent q y) :
    p = q := by
  cases p <;> cases q
  · rfl
  · exact absurd (Iic_eq_univ_of_eq_Ici h) hp
  · refine absurd ?_ hp
    rw [h]
    exact Iic_eq_univ_of_eq_Ici h.symm
  · rfl

-- The whole of a closed scale is an extent of both sorts, which is why (28), (29) ask for proper.
example [BoundedOrder D] : extent .positive (⊤ : D) = extent .negative (⊥ : D) := by
  simp [extent]

/-- On a scale without a maximal element only positive extents are bounded, and a measure phrase
names a bounded extent, so only a positive adjective takes one (p. 266). -/
theorem bddAbove_extent_iff [NoMaxOrder D] : BddAbove (extent p x) ↔ p = .positive := by
  cases p
  · simpa [extent] using bddAbove_Iic
  · simpa [extent] using not_bddAbove_Ici x

end Sorts

/-- An example with the directed scales of its matrix and its standard. -/
structure Compared where
  /-- The directed scale of the matrix adjective. -/
  matrix : Option DirectedScale
  /-- The directed scale of the standard, an adjective or a measure phrase. -/
  standard : Option DirectedScale
  /-- The example. -/
  row : Datum

section Rows

open English.Adjectives English.MeasurePhrases Examples

/-- The directed scale of *mph*, a positive speed. -/
def mph : DirectedScale := (.inl (mile.dimension / hour.dimension), .positive)

-- UNVERIFIED: the labels of `mp_*`, see the module's TODO.
/-- The examples, with the scale of each read from its words. The standard of (73), *shorter than
8 feet*, applies the adjective to the measure phrase, so its scale is that of *short*. -/
def comparisons : List Compared :=
  [⟨long.directedScale?, short.directedScale?, cpa_long_short⟩,
   ⟨short.directedScale?, long.directedScale?, cpa_short_long⟩,
   ⟨wide.directedScale?, long.directedScale?, subdel_pos_pos⟩,
   ⟨short.directedScale?, low.directedScale?, subdel_neg_neg⟩,
   ⟨tall.directedScale?, clever.directedScale?, incomm_tall_clever⟩,
   ⟨tragic.directedScale?, heavy.directedScale?, incomm_tragic_heavy⟩,
   ⟨tall.directedScale?, high.directedScale?, ficus_tall_high⟩,
   ⟨tall.directedScale?, low.directedScale?, ficus_tall_low⟩,
   ⟨short.directedScale?, low.directedScale?, ficus_short_low⟩,
   ⟨short.directedScale?, high.directedScale?, ficus_short_high⟩,
   ⟨long.directedScale?, some foot.directedScale, mp_cadillac⟩,
   ⟨short.directedScale?, some foot.directedScale, mp_fiat⟩,
   ⟨short.directedScale?, short.directedScale?, mp_fiat_comparative⟩,
   ⟨short.directedScale?, some foot.directedScale, mp_reich⟩,
   ⟨slow.directedScale?, some mph, mp_slow⟩]

/-- A comparison is acceptable exactly when its two terms lie in one ordered set, the same scale
in the same sort, which covers incommensurability, cross-polar anomaly and measure phrases at
once. -/
theorem comparison_defined_iff :
    ∀ c ∈ comparisons, c.matrix = c.standard ↔ c.row.judgment = .acceptable := by
  decide

-- Every row of the paper's data is decided.
example : (comparisons.map (·.row.id)).Perm (all.map (·.id)) := by
  decide

end Rows

end Kennedy1999
