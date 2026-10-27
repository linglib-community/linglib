/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Sauerland & Stateva (2011): Two Types of Vagueness

Sauerland and Stateva argue from the distribution of approximators that vagueness comes in two
kinds. Scalar vagueness belongs to terms that denote a point on a scale, such as numerals: a
contextual granularity maps the point to an interval around it, after Krifka, and scalar
approximators such as *exactly* and *approximately* reset the granularity to the finest or the
coarsest available one. Epistemic vagueness belongs to terms like *heap*, whose extension varies
across indistinguishable worlds, and epistemic approximators quantify over those worlds. Within
the scalar class, *absolutely*, *completely* and *more or less* take only scale endpoints and
block *exactly* and *approximately* there.

## Implementation notes

Granularities are the grains `Degree.grain`, identified by their widths, and the
interval a term denotes is the cell of its degree. Cells are half-open so that they partition
the scale; the chapter writes them closed, (12)–(13). The examples at the end check the
intervals of (13) and the oddity of (20).

## References

* [sauerland-stateva-2011]
* [krifka-2007]
* [lasersohn-1999]
-/

@[expose] public section

namespace SauerlandStateva2011

open Degree

/-! ### The two-vagueness classification (§6.3) -/

/-- Their example expressions ((4)–(6), (35), (37), (44)–(45)). -/
inductive Item where
  | fifty
  | three
  | dry
  | full
  | beefStroganoff
  deriving DecidableEq, Repr

/-- The dualistic theory classifies scalar terms as denoting scale points, non-endpoints (numerals)
or endpoints (*dry*, *full*, the closed-scale adjectives of §6.4), and epistemically vague terms as
denoting no point at all. -/
inductive ItemClass where
  | scalarNonEndpoint
  | scalarEndpoint
  | epistemic
  deriving DecidableEq, Repr

/-- Their classification of the example items. -/
def Item.itemClass : Item → ItemClass
  | .fifty | .three => .scalarNonEndpoint
  | .dry | .full => .scalarEndpoint
  | .beefStroganoff => .epistemic

/-- The approximators whose distribution they cite. -/
inductive Approximator where
  | exactly
  | approximately
  | absolutely
  | completely
  | moreOrLess
  deriving DecidableEq, Repr

/-- Plain scalar approximators select non-endpoints, and the endpoint approximators *absolutely*,
*completely* and *more or less*, which make endpoints more or less precise and block *exactly* and
*approximately* there, select endpoints, §6.4 and (32). -/
def Approximator.selects : Approximator → ItemClass
  | .exactly | .approximately => .scalarNonEndpoint
  | .absolutely | .completely | .moreOrLess => .scalarEndpoint

/-- The theory predicts that an approximator combines with an item exactly when the item is of the
class the approximator selects. -/
def compatible (a : Approximator) (i : Item) : Prop :=
  a.selects = i.itemClass

instance (a : Approximator) (i : Item) : Decidable (compatible a i) :=
  inferInstanceAs (Decidable (_ = _))

/-- One cited acceptability judgment. -/
structure Judgment where
  approximator : Approximator
  item : Item
  acceptable : Bool
  deriving Repr

/-- The cited judgments are (4a)/(4b) *exactly/approximately fifty* vs `#`…*Beef Stroganoff*;
(6a)/(6b) `*`*absolutely fifty* vs *absolutely* + endpoint; (35a)/(35b) `#`*exactly dry/full* vs
*exactly three*; (37) *completely dry* vs `#`*completely three*; (44) *approximately three* vs
`#`…*dry*; and (45) *more or less dry* vs `#`…*three*. -/
def Judgment.rows : List Judgment :=
  [⟨.exactly, .fifty, true⟩, ⟨.approximately, .fifty, true⟩,
   ⟨.exactly, .beefStroganoff, false⟩, ⟨.approximately, .beefStroganoff, false⟩,
   ⟨.absolutely, .fifty, false⟩, ⟨.absolutely, .full, true⟩,
   ⟨.exactly, .dry, false⟩, ⟨.exactly, .full, false⟩, ⟨.exactly, .three, true⟩,
   ⟨.completely, .dry, true⟩, ⟨.completely, .three, false⟩,
   ⟨.approximately, .three, true⟩, ⟨.approximately, .dry, false⟩,
   ⟨.moreOrLess, .dry, true⟩, ⟨.moreOrLess, .three, false⟩]

/-- The two-type classification reproduces every cited judgment, an approximator being acceptable
exactly with the class it selects; this is the dualism argument. -/
theorem classification_predicts_distribution :
    ∀ j ∈ Judgment.rows, (compatible j.approximator j.item ↔ j.acceptable) := by
  decide

/-! ### Granularity setting, (12)–(20) -/

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  (𝒢 : Finset α) (h𝒢 : 𝒢.Nonempty) {d ε : α}

/-- At a degree on every available grain, *exactly* yields the narrowest reading (19a), as for *5
meters* in Figure 6.1. -/
theorem exactly_narrowest (hpos : ∀ ε ∈ 𝒢, 0 < ε) (hd : ∀ ε ∈ 𝒢, d ∈ AddSubgroup.zmultiples ε)
    (hε : ε ∈ 𝒢) : (grain (𝒢.min' h𝒢)).cell d ⊆ (grain ε).cell d :=
  cell_grain_subset_cell_grain (hpos _ (𝒢.min'_mem h𝒢)) (𝒢.min'_le ε hε) (hd _ (𝒢.min'_mem h𝒢))
    (hd ε hε)

/-- At a degree that is a scale point of every available granularity, *approximately* yields the
widest available reading, (19b). -/
theorem approximately_widest (hpos : ∀ ε ∈ 𝒢, 0 < ε)
    (hd : ∀ ε ∈ 𝒢, d ∈ AddSubgroup.zmultiples ε) (hε : ε ∈ 𝒢) :
    (grain ε).cell d ⊆ (grain (𝒢.max' h𝒢)).cell d :=
  cell_grain_subset_cell_grain (hpos ε hε) (𝒢.le_max' ε hε) (hd ε hε) (hd _ (𝒢.max'_mem h𝒢))

/-- A second scalar approximator is vacuous, §6.3.5, since the first resets the granularities to a
single one, which either reset returns. -/
theorem second_reset_vacuous {β : Type*} [LinearOrder β] (ε : β) :
    ({ε} : Finset β).min' (Finset.singleton_nonempty ε) = ε ∧
      ({ε} : Finset β).max' (Finset.singleton_nonempty ε) = ε :=
  ⟨Finset.min'_singleton ε, Finset.max'_singleton ε⟩

private theorem cell_of_mul {ε d₀ : ℝ} (k : ℤ) (hk : (k : ℝ) * ε = d₀) (hε : 0 < ε) :
    (grain ε).cell d₀ = Set.Ico (d₀ - ε / 2) (d₀ + ε / 2) := by
  rw [cell_grain hε, representative_eq_self_of_mem_zmultiples hε.ne'
    (AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [zsmul_eq_mul, hk]⟩)]

/-! (13): *5 meters* at 1 m, *4 meters 50* at 50 cm, and *4 meters 90* at 10 cm. -/

example : (grain (1 : ℝ)).cell 5 = Set.Ico (9 / 2) (11 / 2) := by
  rw [cell_of_mul 5 (by norm_num) one_pos]; norm_num

example : (grain (1 / 2 : ℝ)).cell (9 / 2) = Set.Ico (17 / 4) (19 / 4) := by
  rw [cell_of_mul 9 (by norm_num) (by norm_num)]; norm_num

example : (grain (1 / 10 : ℝ)).cell (49 / 10) = Set.Ico (97 / 20) (99 / 20) := by
  rw [cell_of_mul 49 (by norm_num) (by norm_num)]; norm_num

/-! (20): at a coarsest width of ten, *49* and *50* share a cell, which the shorter *50* denotes,
so *approximately 49* is odd. -/

example : (49 : ℝ) ∈ (grain 10).cell 50 := by
  rw [cell_of_mul 5 (by norm_num) (by norm_num)]; norm_num

end SauerlandStateva2011
