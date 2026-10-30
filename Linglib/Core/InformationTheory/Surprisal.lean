/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Surprisal

The surprisal, or information content, of a point under a measure is the negative logarithm of
the mass of the point, an extended nonnegative real: a point of mass zero has infinite surprisal.
The negative logarithm of a product of masses at most one is the sum of their negative logarithms,
and the summand of Shannon entropy at a point is the mass of the point times its surprisal.

## Implementation notes

The surprisal is `-ENNReal.log (μ {s})` truncated at zero by `EReal.toENNReal`, an extended
nonnegative real as `klDiv` is. The truncation only acts on a mass above one, so for a probability
measure the surprisal is exactly the negative logarithm of the mass. Its real part agrees with
`-Real.log (μ.real {s})` wherever the mass is at most one, including a point of mass zero, where
both are `0` (`toReal_surprisal`).

## References

* [cover-thomas-2006], chapter 2.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace ENNReal

/-- The negative logarithm of a product of numbers at most one, truncated at zero, is the sum of
their truncated negative logarithms. -/
theorem toENNReal_neg_log_mul {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) :
    (-log (a * b)).toENNReal = (-log a).toENNReal + (-log b).toENNReal := by
  have hla : log a ≠ ⊤ := log_eq_top_iff.not.2 (ne_top_of_le_ne_top one_ne_top ha)
  have hlb : log b ≠ ⊤ := log_eq_top_iff.not.2 (ne_top_of_le_ne_top one_ne_top hb)
  rw [log_mul_add, EReal.neg_add (Or.inr hlb) (Or.inl hla), sub_eq_add_neg,
    EReal.toENNReal_add (EReal.neg_nonneg.2 (log_le_zero_iff.2 ha))
      (EReal.neg_nonneg.2 (log_le_zero_iff.2 hb))]

end ENNReal

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} {s : S}

/-- The surprisal of the point `s` under the measure `μ`, the negative logarithm of its mass:
infinite at a point of mass zero, and truncated at zero where the mass exceeds one. -/
noncomputable def surprisal (μ : Measure S) (s : S) : ℝ≥0∞ := (-ENNReal.log (μ {s})).toENNReal

@[simp] theorem surprisal_eq_top_iff : surprisal μ s = ∞ ↔ μ {s} = 0 := by
  rw [surprisal, EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff, ENNReal.log_eq_bot_iff]

theorem surprisal_ne_top_iff : surprisal μ s ≠ ∞ ↔ μ {s} ≠ 0 := surprisal_eq_top_iff.not

@[simp] theorem surprisal_eq_zero_iff : surprisal μ s = 0 ↔ 1 ≤ μ {s} := by
  rw [surprisal, EReal.toENNReal_eq_zero_iff, EReal.neg_le, neg_zero, ENNReal.zero_le_log_iff]

theorem surprisal_of_ne_zero (h₀ : μ {s} ≠ 0) (h : μ {s} ≠ ∞) :
    surprisal μ s = ENNReal.ofReal (-Real.log (μ.real {s})) := by
  rw [surprisal, ENNReal.log_pos_real h₀ h, ← EReal.coe_neg, EReal.real_coe_toENNReal,
    measureReal_def]

/-- The real part of the surprisal is the negative logarithm of the real mass wherever the mass is
at most one; at a point of mass zero both are `0`. -/
theorem toReal_surprisal (h : μ {s} ≤ 1) : (surprisal μ s).toReal = -Real.log (μ.real {s}) := by
  rcases eq_or_ne (μ {s}) 0 with h₀ | h₀
  · rw [surprisal_eq_top_iff.2 h₀, measureReal_def, h₀]
    simp
  · have h₁ : μ.real {s} ≤ 1 :=
      measureReal_def μ {s} ▸ ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)
    rw [surprisal_of_ne_zero h₀ (ne_top_of_le_ne_top ENNReal.one_ne_top h),
      ENNReal.toReal_ofReal (neg_nonneg.2 (Real.log_nonpos measureReal_nonneg h₁))]

theorem surprisal_map_of_injective {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
    {f : S → T} (hf : Measurable f) (hi : f.Injective) (μ : Measure S) (s : S) :
    surprisal (μ.map f) (f s) = surprisal μ s := by
  rw [surprisal, surprisal, Measure.map_apply hf (measurableSet_singleton _), ← Set.image_singleton,
    hi.preimage_image]

theorem negMulLog_measureReal_singleton (h : μ {s} ≤ 1) :
    negMulLog (μ.real {s}) = μ.real {s} * (surprisal μ s).toReal := by
  rw [negMulLog, toReal_surprisal h]
  ring

end InformationTheory
