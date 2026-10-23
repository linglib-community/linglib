module

public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Woodin, Winter, Littlemore, Perlman & Grieve (2024): Large-Scale Patterns of Number Use

Woodin et al. model the frequency of numbers in the British National Corpus: the log frequency
of a number is a linear function of its log magnitude and of which roundness properties it has.
The six properties are being a multiple of five or of ten and Jansen and Pollmann's four kinds of
`k`-ness over positive powers of ten. They nest, since 10-ness, 2-ness and 5-ness make a number a
multiple of ten and every property makes it a multiple of five, and with non-negative weights the
predicted frequency is monotone in the roundness ordering of `Numerals.Roundness`.

## Main results

* `dvd_five_of_holds`: every roundness property entails being a multiple of five.
* `predicted_le_iff`: a rounder number of comparable magnitude is predicted more frequent
  exactly when the weights of its extra properties outweigh the magnitude penalty.
* `predicted_99_le_100_iff`: the study's illustration with 99 and 100.

## Implementation notes

The fitted coefficients, the ordering of the properties by effect size, the residual analysis
of culturally salient numbers, and the register comparisons are results of the corpus study
and are not restated here; the theorems are over an arbitrary model, with the sign conditions
the study reports as hypotheses.

## References

* [woodin-etal-2024]
* [jansen-pollmann-2001]
* [sigurd-1988]
-/

@[expose] public section

namespace WoodinEtAl2024

open Numerals.Roundness Finset

/-! ### The roundness properties -/

/-- A roundness property is being a multiple of five or of ten, or one of the four kinds of
`k`-ness. -/
inductive Property where
  | multipleOf5
  | multipleOf10
  | kness (κ : Kness)
  deriving DecidableEq, Repr, Fintype

/-- A number has a roundness property; the `k`-ness properties take a positive power of ten
(footnote 3). -/
def Property.Holds (n : ℕ) : Property → Prop
  | .multipleOf5 => 5 ∣ n
  | .multipleOf10 => 10 ∣ n
  | .kness κ => κ.Holds 1 n

instance (n : ℕ) : DecidablePred (Property.Holds n) := fun p ↦ by
  cases p <;> unfold Property.Holds <;> infer_instance

theorem dvd_ten_of_holds {κ : Kness} {n : ℕ} (hκ : κ ≠ .twoAndAHalf) (h : κ.Holds 1 n) :
    10 ∣ n := by
  cases κ with
  | ten => exact h.dvd
  | two => exact Nat.dvd_trans (by norm_num) h.dvd
  | five => exact Nat.dvd_trans (by norm_num) h.dvd
  | twoAndAHalf => exact absurd rfl hκ

/-- Every roundness property makes a number a multiple of five. -/
theorem dvd_five_of_holds {p : Property} {n : ℕ} (h : p.Holds n) : 5 ∣ n := by
  cases p with
  | multipleOf5 => exact h
  | multipleOf10 => exact Nat.dvd_trans (by norm_num) h
  | kness κ =>
    have h : κ.Holds 1 n := h
    cases κ with
    | twoAndAHalf =>
      have : 50 ∣ 2 * n := h.dvd
      omega
    | _ => exact Nat.dvd_trans (by norm_num) (dvd_ten_of_holds (by decide) h)

/-! ### The frequency model -/

/-- A model of log frequency has a coefficient on log magnitude and a weight per roundness property.
-/
structure Model where
  magnitude : ℝ
  weight : Property → ℝ

namespace Model

variable (M : Model)

/-- The predicted log frequency of a number. -/
noncomputable def predicted (n : ℕ) : ℝ :=
  M.magnitude * Real.logb 10 n + ∑ p ∈ profile Property.Holds n, M.weight p

theorem sum_weight_le_of_atLeastAsRound (hw : ∀ p, 0 ≤ M.weight p) {n m : ℕ}
    (h : AtLeastAsRound Property.Holds n m) :
    ∑ p ∈ profile Property.Holds n, M.weight p ≤ ∑ p ∈ profile Property.Holds m, M.weight p :=
  sum_le_sum_of_subset_of_nonneg (profile_subset_profile.2 h) fun p _ _ ↦ hw p

theorem predicted_anti (hM : M.magnitude ≤ 0) {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (h : profile Property.Holds n = profile Property.Holds m) : M.predicted m ≤ M.predicted n := by
  unfold predicted
  rw [h]
  have := mul_le_mul_of_nonpos_left
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 10) (Nat.cast_pos.mpr hn)
      (Nat.cast_le.mpr hnm)) hM
  linarith

/-- A rounder number is predicted at least as frequent as a less round one exactly when the
weights of its extra properties make up the magnitude difference. -/
theorem predicted_le_iff {n m : ℕ} (h : AtLeastAsRound Property.Holds n m) :
    M.predicted n ≤ M.predicted m ↔
      -M.magnitude * (Real.logb 10 m - Real.logb 10 n) ≤
        ∑ p ∈ profile Property.Holds m \ profile Property.Holds n, M.weight p := by
  unfold predicted
  rw [← sum_sdiff (profile_subset_profile.2 h)]
  constructor <;> intro h' <;> linarith

/-- In the study's illustration 100 has every property and 99 none, so 100 is predicted more
frequent exactly when the summed weights make up the magnitude penalty of one part in a hundred. -/
theorem predicted_99_le_100_iff :
    M.predicted 99 ≤ M.predicted 100 ↔
      -M.magnitude * Real.logb 10 (100 / 99) ≤ ∑ p, M.weight p := by
  have h99 : profile Property.Holds 99 = ∅ := by decide
  have h100 : profile Property.Holds 100 = univ := by decide
  rw [predicted_le_iff M (profile_subset_profile.1 (by rw [h99]; exact empty_subset _)), h99, h100,
    sdiff_empty,
    Real.logb_div (by norm_num) (by norm_num)]
  push_cast
  exact Iff.rfl

end Model

end WoodinEtAl2024
