/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Binomial

import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# The binomial distribution: stochastic order and support

A higher success probability moves the binomial distribution up:
[`Bin(n, p) ≤ₛₜ Bin(n, q)` for `p ≤ q`](##ProbabilityTheory.binomial_stochasticLE). The Bernoulli
measure on a pair `y ≤ x` is monotone in the weight of `x`, the product of Bernoulli measures
that picks a random subset inherits this
([`setBernoulli_stochasticLE`](##ProbabilityTheory.setBernoulli_stochasticLE)), and the binomial
is the law of that subset's cardinality. Strictly between `0` and `1`, the binomial
[charges every count up to `n`](##ProbabilityTheory.binomial_singleton_pos). Both facts are also
stated for `Bin(Fin (n + 1), n, p)`, the binomial on its own support.

[UPSTREAM] candidates for `Mathlib.Probability.Distributions.SetBernoulli` and
`Mathlib.Probability.Distributions.Binomial`.
-/

public section

open MeasureTheory Measure Set unitInterval
open scoped ProbabilityTheory Fin.NatCast

namespace ProbabilityTheory

variable {ι : Type*} [Countable ι] {n : ℕ} {p q : I}

/-- The random subset of `u` that takes each element with probability `p` grows with `p`. -/
theorem setBernoulli_stochasticLE (u : Set ι) (hpq : p ≤ q) : setBer(u, p) ≤ₛₜ setBer(u, q) := by
  choose γ hγ using fun i : ι ↦
    exists_isMonotoneCoupling_bernoulliMeasure (x := i ∈ u) (y := False) False.elim hpq
  rw [setBernoulli_eq_map, setBernoulli_eq_map]
  exact (stochasticLE_infinitePi hγ).map (fun _ _ h i hi ↦ h i hi)
    MeasurableEquiv.setOfPred.measurable

/-- The binomial distribution is stochastically increasing in its success probability. -/
theorem binomial_stochasticLE (n : ℕ) (hpq : p ≤ q) : Bin(n, p) ≤ₛₜ Bin(n, q) := by
  have h : ∀ r : I, ncard =ᵐ[setBer(Iio n, r)] fun s ↦ (s ∩ Iio n).ncard := fun r ↦
    setBernoulli_ae_subset.mono fun s hs ↦ congrArg ncard (inter_eq_left.2 hs).symm
  exact (setBernoulli_stochasticLE _ hpq).map_of_ae_eq
    (fun s t hst ↦ ncard_le_ncard (inter_subset_inter_left _ hst) ((finite_Iio n).inter_of_right _))
    (measurable_ncard.comp <| measurable_set_iff.2 fun a ↦
      (Measurable.of_discrete (f := (· ∧ a ∈ Iio n))).comp (measurable_set_mem a)) (h p) (h q)

theorem map_cast_binomial_fin_stochasticLE (n : ℕ) (hpq : p ≤ q) :
    Bin(Fin (n + 1), n, p) ≤ₛₜ Bin(Fin (n + 1), n, q) := by
  have h : ∀ r : I, (Nat.cast : ℕ → Fin (n + 1)) =ᵐ[Bin(n, r)] fun k ↦ Fin.clamp k n := fun r ↦
    (ae_le_of_hasLaw_binomial (X := id) ⟨aemeasurable_id, map_id⟩).mono fun k hk ↦
      Fin.ext ((Fin.val_cast_of_lt (Nat.lt_succ_of_le hk)).trans (min_eq_left hk).symm)
  exact (binomial_stochasticLE n hpq).map_of_ae_eq
    (fun a b hab ↦ Fin.mk_le_mk.2 (min_le_min_right n hab)) .of_discrete (h p) (h q)

/-- A binomial distribution with success probability strictly between `0` and `1` charges every
count up to `n`. -/
theorem binomial_singleton_pos (hp₀ : 0 < p) (hp₁ : p < 1) {k : ℕ} (hk : k ≤ n) :
    0 < Bin(n, p) {k} := by
  rw [binomial_singleton, ENNReal.ofReal_pos]
  exact mul_pos (mul_pos (Nat.cast_pos.2 (Nat.choose_pos hk)) (pow_pos (coe_pos.2 hp₀) _))
    (pow_pos (sub_pos.2 (coe_lt_one.2 hp₁)) _)

theorem map_cast_binomial_fin_singleton_pos (hp₀ : 0 < p) (hp₁ : p < 1) (k : Fin (n + 1)) :
    0 < Bin(Fin (n + 1), n, p) {k} := by
  rw [map_apply .of_discrete (measurableSet_singleton k)]
  exact (binomial_singleton_pos hp₀ hp₁ k.is_le).trans_le
    (measure_mono (singleton_subset_iff.2 (Fin.cast_val_eq_self k)))

end ProbabilityTheory
