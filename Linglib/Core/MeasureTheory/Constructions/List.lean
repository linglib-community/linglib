/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Infix
public import Linglib.Core.MeasureTheory.Integral.Layercake

/-!
# Measures on lists

Lists carry the discrete σ-algebra. Under a measure on lists the cylinders `x.cylinder`, the lists
beginning with `x`, are counted two ways: [the lists of length at least `n` are partitioned by
their prefix of length `n`](##MeasureTheory.Measure.tsum_measure_cylinder_length), and a list has
one prefix more than its length, so [the total measure of the cylinders is the integral of the
length plus one](##MeasureTheory.Measure.tsum_measure_cylinder).

## Implementation notes

The discrete σ-algebra is registered globally as the library's convention. It is the right one on
lists over a countable type with measurable singletons, the case of strings and of the offspring
of a branching process.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

instance List.instMeasurableSpace {α : Type*} : MeasurableSpace (List α) := ⊤

namespace MeasureTheory.Measure

/-! ### Cylinders -/

section Cylinder

variable {α : Type*} [Countable α] (μ : Measure (List α))

/-- The lists of length at least `n` are partitioned by their prefix of length `n`. -/
theorem tsum_measure_cylinder_length (n : ℕ) :
    ∑' x : {x : List α // x.length = n}, μ x.1.cylinder = μ {y | n ≤ y.length} := by
  rw [show {y : List α | n ≤ y.length} = List.take n ⁻¹' {x | x.length = n} by ext; simp,
    ← tsum_measure_preimage_singleton (Set.to_countable _) fun _ _ ↦ .of_discrete]
  exact tsum_congr fun x ↦ by rw [← x.1.take_preimage_singleton, x.2]

/-- The total measure of the cylinders is the integral of the number of prefixes, the length plus
one. -/
theorem tsum_measure_cylinder :
    ∑' x : List α, μ x.cylinder = ∫⁻ y, (y.length : ℝ≥0∞) + 1 ∂μ := by
  simp_rw [← Nat.cast_add_one]
  rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma',
    lintegral_natCast_eq_tsum_measure_lt (f := fun y : List α ↦ y.length + 1) .of_discrete]
  exact tsum_congr fun n ↦ (tsum_measure_cylinder_length μ n).trans (by simp)

end Cylinder

end MeasureTheory.Measure
