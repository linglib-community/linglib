/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# The hypergeometric distribution

Draw `n` of `N` objects without replacement, `K` of them marked. The number of marked objects
among those drawn is hypergeometric: exactly `k` of them turn up in
`K.choose k * (N - K).choose (n - k)` of the `N.choose n` draws. This file defines the
distribution on `Fin (N + 1)` as a kernel from the number of marked objects to the number drawn.

## Main definitions

* `ProbabilityTheory.hypergeometricCount`: the number of draws with `k` marked objects.
* `ProbabilityTheory.hypergeometric`: the kernel from the number of marked objects to the number
  of marked objects drawn.

## Main results

* `ProbabilityTheory.hypergeometric_real_singleton`: the mass function, by Vandermonde's identity.
* `ProbabilityTheory.hypergeometric_self`: drawing every object is the identity kernel.
* `ProbabilityTheory.posterior_hypergeometric_self`: after drawing every object the posterior is
  the point mass at the number observed.

`[UPSTREAM]` candidate for `Mathlib/Probability/Distributions/`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {N K n k : ℕ}

/-- The number of ways to draw `n` of `N` objects, `K` of them marked, so that exactly `k` marked
objects are drawn. -/
def hypergeometricCount (N K n k : ℕ) : ℕ :=
  if k ≤ n then K.choose k * (N - K).choose (n - k) else 0

theorem hypergeometricCount_ne_zero_iff :
    hypergeometricCount N K n k ≠ 0 ↔ k ≤ n ∧ k ≤ K ∧ n - k ≤ N - K := by
  simp [hypergeometricCount, Nat.choose_ne_zero_iff]

@[simp] theorem hypergeometricCount_zero_zero (N K : ℕ) : hypergeometricCount N K 0 0 = 1 := by
  simp [hypergeometricCount]

theorem hypergeometricCount_self (hK : K ≤ N) (k : ℕ) :
    hypergeometricCount N K N k = if k = K then 1 else 0 := by
  grind [hypergeometricCount_ne_zero_iff, hypergeometricCount, Nat.choose_self]

theorem hypergeometricCount_top (k : ℕ) :
    hypergeometricCount N N n k = if k = n then N.choose n else 0 := by
  grind [hypergeometricCount_ne_zero_iff, hypergeometricCount]

theorem sum_hypergeometricCount (hK : K ≤ N) (hn : n ≤ N) :
    ∑ k : Fin (N + 1), hypergeometricCount N K n k = N.choose n :=
  calc ∑ k : Fin (N + 1), hypergeometricCount N K n k
    _ = ∑ k ∈ Finset.range (N + 1), hypergeometricCount N K n k :=
      Fin.sum_univ_eq_sum_range (hypergeometricCount N K n) (N + 1)
    _ = ∑ k ∈ Finset.range (n + 1), hypergeometricCount N K n k :=
      (Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hn)) fun k _ hk ↦
        ite_eq_right fun h ↦ hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))).symm
    _ = ∑ k ∈ Finset.range (n + 1), K.choose k * (N - K).choose (n - k) :=
      Finset.sum_congr rfl fun k hk ↦ ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    _ = N.choose n := by
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij ↦ K.choose ij.1 * (N - K).choose ij.2), ← Nat.add_choose_eq,
        Nat.add_sub_cancel' hK]

/-- The hypergeometric kernel sends the number of marked objects among `N` to the law of the
number of marked objects among `n` drawn without replacement. -/
noncomputable def hypergeometric (N n : ℕ) : Kernel (Fin (N + 1)) (Fin (N + 1)) :=
  Kernel.ofWeights fun K k ↦ (hypergeometricCount N K n k : ℝ≥0∞)

instance (N n : ℕ) : IsFiniteKernel (hypergeometric N n) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- Drawing every object reveals the number of marked ones. -/
theorem hypergeometric_self : hypergeometric N N = Kernel.id :=
  Kernel.ext fun K ↦ (Kernel.ofWeights_apply_eq_dirac one_ne_zero ENNReal.one_ne_top fun k ↦ by
    simp [hypergeometricCount_self (Nat.lt_succ_iff.1 K.isLt), Fin.ext_iff]).trans
      (Kernel.id_apply K).symm

theorem hypergeometric_last (hn : n ≤ N) :
    hypergeometric N n (Fin.last N) = Measure.dirac ⟨n, Nat.lt_succ_of_le hn⟩ :=
  Kernel.ofWeights_apply_eq_dirac (c := (N.choose n : ℝ≥0∞))
    (Nat.cast_ne_zero.2 (Nat.choose_ne_zero hn)) (ENNReal.natCast_ne_top _) fun k ↦ by
    simp [hypergeometricCount_top, Fin.ext_iff]

section Kernel

variable (K k : Fin (N + 1))

theorem hypergeometric_apply_singleton_ne_zero_iff :
    hypergeometric N n K {k} ≠ 0 ↔ hypergeometricCount N K n k ≠ 0 := by
  rw [hypergeometric, Kernel.ofWeights_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or,
    Nat.cast_eq_zero]
  exact ⟨And.left, fun h ↦ ⟨h, ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.natCast_ne_top _⟩⟩

/-- The hypergeometric mass function. -/
theorem hypergeometric_real_singleton (hn : n ≤ N) :
    (hypergeometric N n K).real {k} = hypergeometricCount N K n k / N.choose n := by
  rw [measureReal_def, hypergeometric, Kernel.ofWeights_apply_singleton, ENNReal.toReal_div,
    ← Nat.cast_sum, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    sum_hypergeometricCount (Nat.lt_succ_iff.1 K.isLt) hn]

/-- After drawing every object, the posterior over the number of marked ones is the point mass at
the number observed. -/
theorem posterior_hypergeometric_self (μ : Measure (Fin (N + 1))) [IsFiniteMeasure μ]
    (hμ : μ {K} ≠ 0) : ((hypergeometric N N)†μ) K = Measure.dirac K := by
  simp only [hypergeometric_self]
  exact (ae_iff_of_countable.1 (posterior_id μ) K hμ).trans (Kernel.id_apply K)

end Kernel

end ProbabilityTheory
