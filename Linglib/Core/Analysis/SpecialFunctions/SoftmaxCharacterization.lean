/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# The softmax function is determined by its odds

A choice rule sends a vector of scores to a distribution over the alternatives. If the odds of any
two alternatives depend on the scores only through the difference of their two scores, and rise
with it, then with at least three alternatives the rule is [the softmax at some inverse
temperature](##Real.exists_eq_softmax_of_div_eq). The condition says that the odds of two
alternatives ignore the scores of the others and ignore a shift of all scores. Three alternatives
turn it into Cauchy's functional equation for the logarithm of the odds, whose [monotone
solutions are linear](##AddMonoidHom.eq_mul_of_monotone). With two alternatives the equation is
vacuous and the rule need not be a softmax.

## References

* [R. D. Luce, *Individual Choice Behavior: A Theoretical Analysis* (1959)][luce-1959]
* [D. McFadden, *Conditional logit analysis of qualitative choice behavior*
  (1974)][mcfadden-1974]
-/

@[expose] public section

open Finset Set

/-- A monotone additive map on the reals is multiplication by its value at one. -/
theorem AddMonoidHom.eq_mul_of_monotone (h : ℝ →+ ℝ) (hh : Monotone h) (s : ℝ) :
    h s = h 1 * s := by
  have hcont : Continuous h :=
    h.continuous_of_isBounded_nhds_zero (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)
      ((Metric.isBounded_Icc (h (-1)) (h 1)).subset hh.image_Icc_subset)
  simpa [mul_comm] using map_real_smul h hcont s 1

namespace Real

variable {ι : Type*} [Fintype ι]

/-- A rule whose odds depend on the scores only through the difference of the two scores, and rise
with it, is the softmax at some inverse temperature, when there are at least three
alternatives. -/
theorem exists_eq_softmax_of_div_eq (hι : 2 < Fintype.card ι) {ρ : (ι → ℝ) → ι → ℝ} {F : ℝ → ℝ}
    (hpos : ∀ s i, 0 < ρ s i) (hsum : ∀ s, ∑ i, ρ s i = 1) (hF : Monotone F)
    (h : ∀ s i j, ρ s i / ρ s j = F (s i - s j)) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ s, ρ s = softmax (α • s) := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk⟩ := Fintype.two_lt_card_iff.1 hι
  have : Nonempty ι := ⟨i⟩
  have hFpos (t : ℝ) : 0 < F t := by
    have ht := h (Function.update 0 i t) i j
    rw [Function.update_self, Function.update_of_ne hij.symm, Pi.zero_apply, sub_zero] at ht
    exact ht ▸ div_pos (hpos _ _) (hpos _ _)
  have hmul (a c : ℝ) : F (a + c) = F a * F c := by
    set s : ι → ℝ := Function.update (Function.update 0 i (a + c)) j c with hs
    have hi : s i = a + c := by rw [hs, Function.update_of_ne hij, Function.update_self]
    have hj : s j = c := Function.update_self ..
    have hk : s k = 0 := by
      rw [hs, Function.update_of_ne hjk.symm, Function.update_of_ne hik.symm, Pi.zero_apply]
    have h1 := h s i k
    have h2 := h s i j
    have h3 := h s j k
    rw [hi, hk, sub_zero] at h1
    rw [hi, hj, add_sub_cancel_right] at h2
    rw [hj, hk, sub_zero] at h3
    rw [← h1, ← h2, ← h3, div_mul_div_cancel₀ (hpos s j).ne']
  let g : ℝ →+ ℝ :=
    { toFun := fun t ↦ log (F t)
      map_zero' := by
        have h0 := congrArg log (hmul 0 0)
        rw [add_zero, log_mul (hFpos 0).ne' (hFpos 0).ne'] at h0
        linarith
      map_add' := fun a c ↦ by rw [hmul, log_mul (hFpos a).ne' (hFpos c).ne'] }
  have hg : Monotone g := fun a c hac ↦ log_le_log (hFpos a) (hF hac)
  have hFexp (t : ℝ) : F t = exp (g 1 * t) := by
    rw [← g.eq_mul_of_monotone hg t]
    exact (exp_log (hFpos t)).symm
  refine ⟨g 1, by simpa using hg zero_le_one, fun s ↦ funext fun i ↦ ?_⟩
  have hρ (j : ι) : ρ s j = ρ s i * exp (g 1 * s j) / exp (g 1 * s i) := by
    have hji := h s j i
    rw [hFexp, mul_sub, exp_sub, div_eq_iff (hpos s i).ne'] at hji
    rw [hji]
    ring
  have h1 := hsum s
  rw [Finset.sum_congr rfl fun j _ ↦ hρ j] at h1
  rw [← Finset.sum_div, ← Finset.mul_sum, div_eq_one_iff_eq (exp_pos _).ne'] at h1
  rw [softmax_apply, eq_div_iff (sum_exp_pos _).ne']
  simpa only [Pi.smul_apply, smul_eq_mul] using h1

end Real
