/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Pearl (2010): Physical and Metaphysical Counterfactuals

The operator `do` of structural models applies to a setting of variables and not to a
disjunction of settings. The report asks what the probability of an outcome is under a
disjunctive action such as *avoid the first restaurant*, and compares two answers.

The structural answer is an interval: the probability lies between the probabilities after the
single actions. For an action chosen at random without regard to the context that is a fact
about averages (`iInf_le_lintegral_le_iSup`).

The answer from imaging lets each agent keep the ratio of her own preferences among the actions
that remain. In the example one taxi driver in ten takes everyone to the third restaurant and
the others take eight customers in nine to the first and one to the second. Told to avoid the
first, the drivers of the first kind go to the third and the others to the second, so the
second restaurant has probability nine tenths (`avoidFirst_second`), where conditioning on the
disjunction, which keeps the ratio of the marginal preferences, gives one half
(`marginal_second`).

## Implementation notes

A choice of action that depends on the context is a function from contexts to measures on
actions, and the probability of an outcome is the integral over contexts of the measure of the
actions that lead to it. A choice that reads the context can leave the interval of the
structural answer.

## References

* [pearl-2010]
* [pearl-2000]
-/

@[expose] public section

namespace Pearl2010

open MeasureTheory
open scoped ENNReal

/-- For an action chosen at random without regard to the context, the average of a quantity
lies between its least and its greatest value over the actions. -/
theorem iInf_le_lintegral_le_iSup {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → ℝ≥0∞) :
    ⨅ x, f x ≤ ∫⁻ x, f x ∂μ ∧ ∫⁻ x, f x ∂μ ≤ ⨆ x, f x := by
  constructor
  · calc ⨅ x, f x = ∫⁻ _, ⨅ x, f x ∂μ := by simp
      _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono fun x ↦ iInf_le f x
  · calc ∫⁻ x, f x ∂μ ≤ ∫⁻ _, ⨆ x, f x ∂μ := lintegral_mono fun x ↦ le_iSup f x
      _ = ⨆ x, f x := by simp

/-! ### The taxi drivers -/

/-- The two kinds of driver. -/
inductive Driver | z₁ | z₂
  deriving DecidableEq

/-- The three restaurants. -/
inductive Restaurant | x₁ | x₂ | x₃
  deriving DecidableEq

instance : MeasurableSpace Driver := ⊤
instance : MeasurableSingletonClass Driver := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Restaurant := ⊤
instance : MeasurableSingletonClass Restaurant := ⟨fun _ ↦ trivial⟩

/-- One driver in ten is of the first kind. -/
noncomputable def drivers : Measure Driver :=
  (10⁻¹ : ℝ≥0∞) • Measure.dirac Driver.z₁ + (9 / 10 : ℝ≥0∞) • Measure.dirac Driver.z₂

/-- Each driver's choice between the second and third restaurants, in the ratio of her own
preferences. -/
noncomputable def avoidFirst : Driver → Measure Restaurant
  | .z₁ => Measure.dirac Restaurant.x₃
  | .z₂ => Measure.dirac Restaurant.x₂

/-- Eq. (16): with each driver following her own preferences, the second restaurant has
probability nine tenths. -/
theorem avoidFirst_second : ∫⁻ z, avoidFirst z {Restaurant.x₂} ∂drivers = 9 / 10 := by
  rw [drivers, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp [avoidFirst]

theorem drivers_univ : drivers Set.univ = 1 := by
  have h : (10⁻¹ : ℝ≥0∞) + 9 / 10 = 1 := by
    rw [div_eq_mul_inv]
    nth_rewrite 1 [← one_mul (10⁻¹ : ℝ≥0∞)]
    rw [← add_mul]
    norm_num
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  simp [drivers, h]

/-- Eq. (15): the even choice between the two restaurants, made without regard to the driver,
gives the second restaurant probability one half. -/
theorem marginal_second :
    ∫⁻ _, ((2⁻¹ : ℝ≥0∞) • Measure.dirac Restaurant.x₂ +
      (2⁻¹ : ℝ≥0∞) • Measure.dirac Restaurant.x₃) {Restaurant.x₂} ∂drivers = 2⁻¹ := by
  rw [lintegral_const, drivers_univ, mul_one]
  simp

end Pearl2010
