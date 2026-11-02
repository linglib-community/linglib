/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Distributions.Binomial

/-!
# The binomial distribution on `Fin (n + 1)`

The binomial distribution `Bin(n, p)` cast into `Fin (n + 1)` gives each point `k` the mass
`n.choose k * p ^ k * (1 - p) ^ (n - k)`: the cast is injective on the support `Set.Iic n`, so
the `Bin(R, n, p)` formulas, stated in mathlib for `CharZero R`, hold for the finite carrier.

## Main results

* `ProbabilityTheory.map_cast_binomial_fin_singleton`,
  `ProbabilityTheory.map_cast_binomial_fin_real_singleton`: the mass at a point of
  `Bin(Fin (n + 1), n, p)`.

[UPSTREAM] candidates for `Mathlib.Probability.Distributions.Binomial`.
-/

public section

open MeasureTheory unitInterval
open scoped ProbabilityTheory Fin.NatCast

namespace ProbabilityTheory

variable (n : ℕ) (p : I)

theorem map_cast_binomial_fin_singleton (k : Fin (n + 1)) :
    Bin(Fin (n + 1), n, p) {k}
      = ENNReal.ofReal ((n.choose k) * (p : ℝ) ^ (k : ℕ) * (1 - p) ^ (n - k)) := by
  rw [map_cast_binomial_eq_sum_dirac, Measure.finsetSum_apply,
    Finset.sum_eq_single (k : ℕ) (λ j hj hjk => ?_) (λ h => absurd (Finset.mem_Iic.mpr k.is_le) h)]
  · rw [Measure.smul_apply, Fin.cast_val_eq_self, Measure.dirac_apply_of_mem (Set.mem_singleton k),
      smul_eq_mul, mul_one]
  · rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton k),
      Set.indicator_of_notMem, smul_zero]
    rw [Set.mem_singleton_iff, Fin.ext_iff, Fin.val_natCast,
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le (Finset.mem_Iic.mp hj))]
    exact hjk

theorem map_cast_binomial_fin_real_singleton (k : Fin (n + 1)) :
    Bin(Fin (n + 1), n, p).real {k} = (n.choose k) * (p : ℝ) ^ (k : ℕ) * (1 - p) ^ (n - k) := by
  rw [measureReal_def, map_cast_binomial_fin_singleton, ENNReal.toReal_ofReal binomial_nonneg]

end ProbabilityTheory
