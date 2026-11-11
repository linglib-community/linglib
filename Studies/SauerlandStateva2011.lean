/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Granularity
public import Linglib.Fragments.English.Adjectives
public import Linglib.Data.Examples.SauerlandStateva2011
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Sauerland & Stateva (2011): Two Types of Vagueness

Sauerland and Stateva argue from the distribution of approximators that vagueness comes in two
kinds. A scalar term such as a numeral denotes a point on a scale, which a contextual granularity
maps to an interval around it, after Krifka; an epistemically vague term such as *beef
Stroganoff* denotes none. *Exactly* resets the granularity to [the finest available
grain](##exactly_narrowest) and *approximately* to the coarsest, so [a second approximator is
vacuous](##reset_reset). *Completely* and *more or less* apply at the maximum of an adjective's
scale and block *exactly* and *approximately* wherever they apply, which [predicts the cited
distribution](##acceptable_iff_judgment) from the scales of the terms.

## Implementation notes

Granularities are the grains `grain`, identified by their widths, and the interval a term
denotes is the cell of its degree. Cells are half-open so that they partition the scale; the
chapter writes them closed, (12)–(13). A term is given by the endpoints of the scale it denotes a
point on, `none` for an epistemically vague one: a numeral's scale is the order of `ℕ`, an
adjective's that of its English fragment entry. *Absolutely* and *totally* share the entry of
*completely* (p. 135). The rows are the cited judgments on terms with fragment entries.

## References

* [sauerland-stateva-2011]
* [krifka-2007]
* [kennedy-mcnally-2005]
* [lasersohn-1999]
-/

@[expose] public section

namespace SauerlandStateva2011

open English.Adjectives

/-! ### Scalar approximators, (19), (38), (46) -/

/-- The granularity a scalar approximator resets to, (19). -/
inductive Setting where
  | finest
  | coarsest
  deriving DecidableEq, Repr

/-- A scalar approximator applies at any point of a scale, as *exactly* (19a), or at the maximum
of an adjective's scale, as *completely* (38). -/
inductive Target where
  | point
  | maximum
  deriving DecidableEq, Repr

/-- A scalar approximator resets the granularity of its complement and applies at a point or at a
maximum. -/
structure Approximator where
  /-- The granularity it resets to. -/
  setting : Setting
  /-- Where on the scale it applies. -/
  target : Target
  deriving DecidableEq, Repr

/-- *exactly*, (19a). -/
def exactly : Approximator := ⟨.finest, .point⟩

/-- *approximately*, (19b). -/
def approximately : Approximator := ⟨.coarsest, .point⟩

/-- *completely*, (38). -/
def completely : Approximator := ⟨.finest, .maximum⟩

/-- *more or less*, (46). -/
def moreOrLess : Approximator := ⟨.coarsest, .maximum⟩

/-- A numeral denotes a point on the order of the natural numbers. -/
noncomputable def numeral : Option Boundedness := some (.ofOrder ℕ)

namespace Approximator

/-- An approximator applies to a term that denotes a point, and one that targets the maximum
only to a term whose scale has one. -/
def Applies : Approximator → Option Boundedness → Prop
  | _, none => False
  | ⟨_, .point⟩, some _ => True
  | ⟨_, .maximum⟩, some b => b.HasMax

instance instDecidableApplies : ∀ a s, Decidable (Applies a s)
  | _, none => isFalse id
  | ⟨_, .point⟩, some _ => isTrue trivial
  | ⟨_, .maximum⟩, some b => inferInstanceAs (Decidable b.HasMax)

/-- An approximator is acceptable where it applies, unless it targets a point and the
approximator of its granularity that targets the maximum also applies, which blocks it
(§6.4.1). -/
def Acceptable (a : Approximator) (s : Option Boundedness) : Prop :=
  a.Applies s ∧ (a.target = .point → ¬ (⟨a.setting, .maximum⟩ : Approximator).Applies s)

instance (a : Approximator) (s : Option Boundedness) : Decidable (a.Acceptable s) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Approximator

private theorem ofOrder_nat : Boundedness.ofOrder ℕ = .lowerClosed :=
  Boundedness.ext (iff_of_true Boundedness.hasMin_ofOrder_of_orderBot trivial)
    (iff_of_false Boundedness.not_hasMax_ofOrder id)

/-- The cited judgments: an approximator, the term it modifies and the row. -/
noncomputable def judged : List (Approximator × Option Boundedness × Datum) :=
  [(exactly, numeral, Examples.ex_4a_exactly),
   (approximately, numeral, Examples.ex_4a_approximately),
   (exactly, none, Examples.ex_4b_exactly), (approximately, none, Examples.ex_4b_approximately),
   (completely, numeral, Examples.ex_6a_absolutely),
   (completely, numeral, Examples.ex_6a_completely), (completely, numeral, Examples.ex_6a_totally),
   (completely, full.boundedness, Examples.ex_32a_absolutely),
   (exactly, full.boundedness, Examples.ex_32a_exactly),
   (exactly, dry.boundedness, Examples.ex_35a_dry),
   (exactly, full.boundedness, Examples.ex_35a_full),
   (exactly, empty.boundedness, Examples.ex_35a_empty), (exactly, numeral, Examples.ex_35b_three),
   (exactly, none, Examples.ex_35c_stroganoff), (exactly, none, Examples.ex_35c_heap),
   (completely, dry.boundedness, Examples.ex_37a_dry), (completely, numeral, Examples.ex_37b_three),
   (completely, none, Examples.ex_37c_stroganoff), (completely, none, Examples.ex_37c_heap),
   (approximately, dry.boundedness, Examples.ex_44a_dry),
   (approximately, numeral, Examples.ex_44b_three),
   (approximately, none, Examples.ex_44c_stroganoff), (approximately, none, Examples.ex_44c_heap),
   (moreOrLess, dry.boundedness, Examples.ex_45a_dry), (moreOrLess, numeral, Examples.ex_45b_three),
   (moreOrLess, none, Examples.ex_45c_stroganoff), (moreOrLess, none, Examples.ex_45c_heap),
   (exactly, closed_.boundedness, Examples.p132_closed)]

/-- The entries of the approximators and the scales of the terms predict every cited judgment:
*exactly* and *approximately* combine with numerals, *completely* and *more or less* with
adjectives whose scale has a maximum, and none with an epistemically vague term. -/
theorem acceptable_iff_judgment :
    ∀ r ∈ judged, (r.1.Acceptable r.2.1 ↔ r.2.2.judgment = .acceptable) := by
  simp only [judged, numeral, ofOrder_nat]
  decide

/-- *More or less* needs a maximum and *wet* has only a minimum, so *approximately wet* is
unblocked, against the judgment of §6.4.1. -/
theorem approximately_wet :
    approximately.Acceptable wet.boundedness ∧ Examples.p132_wet.judgment ≠ .acceptable := by
  decide

/-! ### Granularity setting, (12)–(20) -/

/-- The width of the grain an approximator of the setting resets the available grains to, (19). -/
def Setting.reset {β : Type*} [LinearOrder β] : Setting → (𝒢 : Finset β) → 𝒢.Nonempty → β
  | .finest, 𝒢, h => 𝒢.min' h
  | .coarsest, 𝒢, h => 𝒢.max' h

/-- A second scalar approximator is vacuous, as the oddity of (27) shows (§6.3.5): the first
resets the grains to a single one, which the second returns. -/
theorem reset_reset {β : Type*} [LinearOrder β] (s t : Setting) (𝒢 : Finset β)
    (h : 𝒢.Nonempty) : t.reset {s.reset 𝒢 h} (Finset.singleton_nonempty _) = s.reset 𝒢 h := by
  cases t
  · exact Finset.min'_singleton _
  · exact Finset.max'_singleton _

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  (𝒢 : Finset α) (h𝒢 : 𝒢.Nonempty) {d ε : α}

/-- At a degree on every available grain, *exactly* yields the narrowest reading (19a), as for *5
meters* in Figure 6.1. -/
theorem exactly_narrowest (hpos : ∀ ε ∈ 𝒢, 0 < ε) (hd : ∀ ε ∈ 𝒢, d ∈ AddSubgroup.zmultiples ε)
    (hε : ε ∈ 𝒢) : (grain (exactly.setting.reset 𝒢 h𝒢)).cell d ⊆ (grain ε).cell d :=
  cell_grain_subset_cell_grain (hpos _ (𝒢.min'_mem h𝒢)) (𝒢.min'_le ε hε) (hd _ (𝒢.min'_mem h𝒢))
    (hd ε hε)

/-- At a degree that is a scale point of every available granularity, *approximately* yields the
widest available reading, (19b). -/
theorem approximately_widest (hpos : ∀ ε ∈ 𝒢, 0 < ε)
    (hd : ∀ ε ∈ 𝒢, d ∈ AddSubgroup.zmultiples ε) (hε : ε ∈ 𝒢) :
    (grain ε).cell d ⊆ (grain (approximately.setting.reset 𝒢 h𝒢)).cell d :=
  cell_grain_subset_cell_grain (hpos ε hε) (𝒢.le_max' ε hε) (hd ε hε) (hd _ (𝒢.max'_mem h𝒢))

/-! (13): *5 meters* at 1 m, *4 meters 50* at 50 cm, and *4 meters 90* at 10 cm. -/

example : (grain (1 : ℝ)).cell 5 = Set.Ico (9 / 2) (11 / 2) := by
  rw [cell_grain_of_mem_zmultiples one_pos (AddSubgroup.mem_zmultiples_iff.2 ⟨5, by norm_num⟩)]
  norm_num

example : (grain (1 / 2 : ℝ)).cell (9 / 2) = Set.Ico (17 / 4) (19 / 4) := by
  rw [cell_grain_of_mem_zmultiples (by norm_num)
    (AddSubgroup.mem_zmultiples_iff.2 ⟨9, by norm_num⟩)]
  norm_num

example : (grain (1 / 10 : ℝ)).cell (49 / 10) = Set.Ico (97 / 20) (99 / 20) := by
  rw [cell_grain_of_mem_zmultiples (by norm_num)
    (AddSubgroup.mem_zmultiples_iff.2 ⟨49, by norm_num⟩)]
  norm_num

/-! (20): at a coarsest width of ten, *49* and *50* share a cell, which the shorter *50* denotes,
so *approximately 49* is odd. -/

example : (49 : ℝ) ∈ (grain 10).cell 50 := by
  rw [cell_grain_of_mem_zmultiples (by norm_num)
    (AddSubgroup.mem_zmultiples_iff.2 ⟨5, by norm_num⟩)]
  norm_num

end SauerlandStateva2011
