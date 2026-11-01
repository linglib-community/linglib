module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Printed statistics: schema

The primitive values of `Data/Statistics/<Paper>.lean`, the per-paper modules that
`scripts/gen_statistics.py` generates from `Data/Statistics/<Paper>.json`. A paper's own coding
labels (its factors, response types, predictors) become generated enums, and each table it
prints becomes a generated structure with one row per printed line; this file holds only what
every paper shares.

This is data: it imports nothing from `Linglib/` and states no theorems about theories.
A statistic is kept as printed, `Decimal` recording the digits so that `75` and `75.0` differ,
and a study reads it through `Decimal.toRat`. A p-value is a `PValue`, kept with the relation it
is printed with, so that `p < .05` and `p = .05` differ, and read at a level through
`PValue.Significant`. What a study concludes from the numbers (a prototype, a preference, the
effects it counts as found) is a definition in the study, not a stored label.
-/

@[expose] public section

namespace Data.Statistics

/-- A decimal as printed: the value `mantissa / 10 ^ exponent`, with `exponent` the place of the
last printed digit, the number of decimal places or the `k` of a printed power of ten `10^-k`. -/
structure Decimal where
  mantissa : ℤ
  exponent : ℕ
  deriving DecidableEq, Repr

namespace Decimal

/-- The printed value. -/
def toRat (d : Decimal) : ℚ := d.mantissa / 10 ^ d.exponent

@[simp] theorem toRat_pos (d : Decimal) : 0 < d.toRat ↔ 0 < d.mantissa := by
  simp [toRat, pow_pos]

@[simp] theorem toRat_neg (d : Decimal) : d.toRat < 0 ↔ d.mantissa < 0 := by
  simp [toRat, div_neg_iff, pow_pos]

instance (d : Decimal) : Decidable (0 < d.toRat) := decidable_of_iff' _ (toRat_pos d)

instance (d : Decimal) : Decidable (d.toRat < 0) := decidable_of_iff' _ (toRat_neg d)

/-- The printed value in hundredths, exact when at most two places are printed: a proportion
printed to two places, in percent. -/
def hundredths (d : Decimal) : ℤ := d.mantissa * 100 / 10 ^ d.exponent

/-- The printed value is the proportion `k / n` rounded to the printed places: the two differ by
at most half a unit in the last printed place. -/
def Rounds (d : Decimal) (k n : ℕ) : Prop :=
  2 * |(10 ^ d.exponent * k : ℤ) - d.mantissa * n| ≤ n

instance (d : Decimal) (k n : ℕ) : Decidable (d.Rounds k n) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem rounds_iff {d : Decimal} {k n : ℕ} (hn : 0 < n) :
    d.Rounds k n ↔ |(k / n : ℚ) - d.toRat| ≤ 1 / (2 * 10 ^ d.exponent) := by
  have h10 : (0 : ℚ) < 10 ^ d.exponent := pow_pos (by norm_num) _
  have hn' : (0 : ℚ) < n := Nat.cast_pos.2 hn
  rw [toRat, div_sub_div _ _ hn'.ne' h10.ne', abs_div, abs_of_pos (mul_pos hn' h10),
    div_le_div_iff₀ (mul_pos hn' h10) (mul_pos two_pos h10), one_mul, mul_comm (2 : ℚ),
    ← mul_assoc, mul_right_comm _ (10 ^ d.exponent : ℚ), mul_le_mul_iff_of_pos_right h10,
    Rounds, ← @Int.cast_le ℚ]
  push_cast
  rw [mul_comm (k : ℚ), mul_comm (n : ℚ), mul_comm _ (2 : ℚ)]

/-- The printed value is the percentage `100 * k / n` rounded to the printed places. -/
def RoundsPercent (d : Decimal) (k n : ℕ) : Prop := d.Rounds (100 * k) n

instance (d : Decimal) (k n : ℕ) : Decidable (d.RoundsPercent k n) :=
  inferInstanceAs (Decidable (d.Rounds _ _))

/-- Some count out of `n` rounds to the printed percentage. -/
def AttainablePercent (d : Decimal) (n : ℕ) : Prop := ∃ k : Fin (n + 1), d.RoundsPercent k n

instance (d : Decimal) (n : ℕ) : Decidable (d.AttainablePercent n) :=
  inferInstanceAs (Decidable (∃ _, _))

end Decimal

/-- A p-value as printed: the relation `compare p value` it is printed with and the printed
value, `p < .001` as `⟨.lt, ⟨1, 3⟩⟩` and `p = .03` as `⟨.eq, ⟨3, 2⟩⟩`. -/
structure PValue where
  relation : Ordering
  value : Decimal
  deriving DecidableEq, Repr

namespace PValue

variable {v : Decimal} {α : ℚ}

/-- A printed p-value is significant at level `α` when every p-value it allows is below `α`. -/
def Significant (p : PValue) (α : ℚ) : Prop :=
  ∀ q : ℚ, compare q p.value.toRat = p.relation → q < α

@[simp] theorem significant_lt : (⟨.lt, v⟩ : PValue).Significant α ↔ v.toRat ≤ α := by
  simp only [Significant, compare_lt_iff_lt]
  exact forall_lt_iff_le

@[simp] theorem significant_eq : (⟨.eq, v⟩ : PValue).Significant α ↔ v.toRat < α := by
  simp [Significant]

@[simp] theorem not_significant_gt : ¬ (⟨.gt, v⟩ : PValue).Significant α := fun h ↦ by
  obtain ⟨q, hq⟩ := exists_gt (max v.toRat α)
  exact (h q (compare_gt_iff_gt.2 ((le_max_left _ _).trans_lt hq))).not_ge
    ((le_max_right _ _).trans hq.le)

instance (p : PValue) (α : ℚ) : Decidable (p.Significant α) :=
  match p with
  | ⟨.lt, _⟩ => decidable_of_iff' _ significant_lt
  | ⟨.eq, _⟩ => decidable_of_iff' _ significant_eq
  | ⟨.gt, _⟩ => isFalse not_significant_gt

end PValue

/-- The sign of a binary feature in the `[+F]` / `[-F]` notation. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq, Repr

end Data.Statistics
