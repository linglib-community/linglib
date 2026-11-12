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

The exponential is also forced by independence. A ratio rule gives each alternative a strength
that depends on its score and chooses in proportion to strength. If the rule on a pair of
independent binary choices, scored by the sum of the two scores, is the product of the rules on
each, then [the strength is exponential in the score](##Real.exists_eq_mul_exp_of_div_sum_mul).

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

/-- A ratio rule that treats independent choices independently has exponential strength. If
choosing in proportion to `g` of the score, on two binary choices scored by the sum of their
scores, is the product of doing so on each, then `g` is an exponential. -/
theorem exists_eq_mul_exp_of_div_sum_mul {g : ℝ → ℝ} (hpos : ∀ x, 0 < g x) (hg : Monotone g)
    (h : ∀ (s t : Bool → ℝ) (i k : Bool),
      g (s i + t k) / ∑ p : Bool × Bool, g (s p.1 + t p.2) =
        g (s i) / (∑ j, g (s j)) * (g (t k) / ∑ l, g (t l))) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ x, g x = g 0 * exp (α * x) := by
  have hmul (x y : ℝ) : g (x + y) * g 0 = g x * g y := by
    set s : Bool → ℝ := fun b ↦ cond b x 0 with hs
    set t : Bool → ℝ := fun b ↦ cond b y 0 with ht
    have hD : 0 < ∑ p : Bool × Bool, g (s p.1 + t p.2) :=
      Finset.sum_pos (fun _ _ ↦ hpos _) Finset.univ_nonempty
    have hA : 0 < ∑ j, g (s j) := Finset.sum_pos (fun _ _ ↦ hpos _) Finset.univ_nonempty
    have hB : 0 < ∑ l, g (t l) := Finset.sum_pos (fun _ _ ↦ hpos _) Finset.univ_nonempty
    have e1 : g (x + y) * ((∑ j, g (s j)) * ∑ l, g (t l)) =
        g x * g y * ∑ p : Bool × Bool, g (s p.1 + t p.2) := by
      have := h s t true true
      rw [div_mul_div_comm, div_eq_div_iff hD.ne' (mul_pos hA hB).ne'] at this
      exact this
    have e2 : g (0 + 0) * ((∑ j, g (s j)) * ∑ l, g (t l)) =
        g 0 * g 0 * ∑ p : Bool × Bool, g (s p.1 + t p.2) := by
      have := h s t false false
      rw [div_mul_div_comm, div_eq_div_iff hD.ne' (mul_pos hA hB).ne'] at this
      exact this
    rw [add_zero, mul_assoc] at e2
    have hAB := mul_left_cancel₀ (hpos 0).ne' e2
    exact mul_right_cancel₀ hD.ne' (by rw [mul_assoc, ← hAB, e1])
  let f : ℝ →+ ℝ :=
    { toFun := fun x ↦ log (g x) - log (g 0)
      map_zero' := sub_self _
      map_add' := fun x y ↦ by
        have hxy := congrArg log (hmul x y)
        rw [log_mul (hpos _).ne' (hpos 0).ne', log_mul (hpos x).ne' (hpos y).ne'] at hxy
        linarith }
  have hf : Monotone f := fun x y hxy ↦ sub_le_sub_right (log_le_log (hpos x) (hg hxy)) _
  refine ⟨f 1, by simpa using hf zero_le_one, fun x ↦ ?_⟩
  have hx : log (g x) - log (g 0) = f 1 * x := f.eq_mul_of_monotone hf x
  rw [← exp_log (hpos x), ← exp_log (hpos 0), ← exp_add]
  congr 1
  linarith

end Real
