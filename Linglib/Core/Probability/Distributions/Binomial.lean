/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Probability.Distributions.Binomial

/-!
# The binomial distribution on a carrier without characteristic zero

Mathlib computes the point masses of `Bin(R, n, p)` for `CharZero R`. Characteristic zero is used
only to keep the casts of `0, …, n` apart, so the same formula holds whenever
[the cast is injective there](##ProbabilityTheory.map_cast_binomial_singleton_of_injOn).
On `Fin (n + 1)` it is, which gives
[the mass at every point](##ProbabilityTheory.map_cast_binomial_fin_singleton) of
`Bin(Fin (n + 1), n, p)`, the binomial distribution on its own support.

[UPSTREAM] candidates for `Mathlib.Probability.Distributions.Binomial`.
-/

public section

open MeasureTheory unitInterval
open scoped ProbabilityTheory Fin.NatCast

namespace ProbabilityTheory

section InjOn

variable {R : Type*} [MeasurableSpace R] [AddMonoidWithOne R] [MeasurableSingletonClass R]
  {n k : ℕ} (p : I)

/-- The mass `Bin(R, n, p)` gives the cast of `k ≤ n`, when the cast separates `0, …, n`. -/
theorem map_cast_binomial_singleton_of_injOn (h : Set.InjOn (Nat.cast : ℕ → R) (Set.Iic n))
    (hk : k ≤ n) :
    Bin(R, n, p) {(k : R)} = ENNReal.ofReal (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) := by
  rw [map_cast_binomial_eq_sum_dirac, Measure.finsetSum_apply,
    Finset.sum_eq_single k (fun j hj hjk ↦ ?_) (absurd (Finset.mem_Iic.mpr hk)),
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul, mul_one]
  rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator_of_notMem (fun hj' : (j : R) ∈ ({(k : R)} : Set R) ↦
      hjk (h (Finset.mem_Iic.mp hj) hk hj')), smul_zero]

theorem map_cast_binomial_real_singleton_of_injOn (h : Set.InjOn (Nat.cast : ℕ → R) (Set.Iic n))
    (hk : k ≤ n) :
    Bin(R, n, p).real {(k : R)} = n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k) := by
  rw [measureReal_def, map_cast_binomial_singleton_of_injOn p h hk,
    ENNReal.toReal_ofReal binomial_nonneg]

end InjOn

variable (n : ℕ) (p : I)

/-- The mass at a point of the binomial distribution on its support `Fin (n + 1)`. -/
theorem map_cast_binomial_fin_singleton (k : Fin (n + 1)) :
    Bin(Fin (n + 1), n, p) {k}
      = ENNReal.ofReal (n.choose k * (p : ℝ) ^ (k : ℕ) * (1 - p) ^ (n - k)) := by
  simpa using map_cast_binomial_singleton_of_injOn p
    ((CharP.natCast_injOn_Iio (Fin (n + 1)) (n + 1)).mono fun _ ↦ Nat.lt_succ_of_le) k.is_le

theorem map_cast_binomial_fin_real_singleton (k : Fin (n + 1)) :
    Bin(Fin (n + 1), n, p).real {k} = n.choose k * (p : ℝ) ^ (k : ℕ) * (1 - p) ^ (n - k) := by
  rw [measureReal_def, map_cast_binomial_fin_singleton, ENNReal.toReal_ofReal binomial_nonneg]

end ProbabilityTheory
