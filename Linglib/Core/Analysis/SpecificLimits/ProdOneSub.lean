/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Vanishing products of `1 - a n`

For a sequence with `0 ≤ a n ≤ 1`, the partial products `∏ k < n, (1 - a k)` tend to zero exactly
when some factor vanishes or the series `∑ a n` diverges. When the series diverges, the products
are squeezed below `exp (-∑ k < n, a k)`; when it converges and no factor vanishes, they converge
to a nonzero infinite product.

## Main results

* `Real.tendsto_prod_range_one_sub_nhds_zero_iff`
* `ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff`
-/

public section

open Filter Finset Topology
open scoped ENNReal

namespace Real

theorem tendsto_prod_range_one_sub_nhds_zero_iff {a : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n)
    (h1 : ∀ n, a n ≤ 1) :
    Tendsto (fun n ↦ ∏ k ∈ range n, (1 - a k)) atTop (𝓝 0) ↔ (∃ n, a n = 1) ∨ ¬ Summable a := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra! hc
    obtain ⟨hne, hs⟩ := hc
    have hu : Summable fun n ↦ ‖-a n‖ := by simpa [abs_of_nonneg (h0 _)] using hs
    have hf : ∀ n, 1 + -a n ≠ 0 := fun n ↦ by
      rw [← sub_eq_add_neg]; exact sub_ne_zero.2 (hne n).symm
    refine tprod_one_add_ne_zero_of_summable hf hu (tendsto_nhds_unique ?_ h)
    simpa [sub_eq_add_neg] using (multipliable_one_add_of_summable hu).hasProd.tendsto_prod_nat
  · rintro (⟨n, hn⟩ | hs)
    · refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n + 1, fun m hm ↦ ?_⟩)
      exact (prod_eq_zero (i := n) (mem_range.2 (by omega)) (by simp [hn])).symm
    · have hexp : Tendsto (fun n ↦ exp (-∑ k ∈ range n, a k)) atTop (𝓝 0) :=
        tendsto_exp_neg_atTop_nhds_zero.comp
          ((not_summable_iff_tendsto_nat_atTop_of_nonneg h0).1 hs)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
        (fun n ↦ prod_nonneg fun k _ ↦ sub_nonneg.2 (h1 k)) fun n ↦ ?_
      rw [← sum_neg_distrib, exp_sum]
      exact prod_le_prod₀ (fun k _ ↦ sub_nonneg.2 (h1 k)) fun k _ ↦ by
        linarith [add_one_le_exp (-a k)]

end Real

namespace ENNReal

theorem tendsto_prod_range_one_sub_nhds_zero_iff {a : ℕ → ℝ≥0∞} (h1 : ∀ n, a n ≤ 1) :
    Tendsto (fun n ↦ ∏ k ∈ range n, (1 - a k)) atTop (𝓝 0) ↔ (∃ n, a n = 1) ∨ ∑' n, a n = ∞ := by
  have hfin : ∀ n, a n ≠ ∞ := fun n ↦ ne_top_of_le_ne_top one_ne_top (h1 n)
  have hprod : ∀ n, ∏ k ∈ range n, (1 - a k) ≠ ∞ := fun n ↦
    prod_ne_top fun k _ ↦ sub_ne_top one_ne_top
  have htoReal (n : ℕ) :
      (∏ k ∈ range n, (1 - a k)).toReal = ∏ k ∈ range n, (1 - (a k).toReal) := by
    rw [toReal_prod]
    refine prod_congr rfl fun k _ ↦ ?_
    rw [toReal_sub_of_le (h1 k) one_ne_top, toReal_one]
  rw [← tendsto_toReal_iff hprod zero_ne_top, toReal_zero]
  simp_rw [htoReal]
  rw [Real.tendsto_prod_range_one_sub_nhds_zero_iff (fun n ↦ toReal_nonneg)
    (fun n ↦ toReal_le_of_le_ofReal zero_le_one (by simpa using h1 n))]
  refine or_congr (exists_congr fun n ↦ toReal_eq_one_iff _) ⟨fun hs ↦ ?_, fun h hs ↦ ?_⟩
  · by_contra h
    exact hs (summable_toReal h)
  · have := ofReal_tsum_of_nonneg (fun n ↦ toReal_nonneg) hs
    simp_rw [ofReal_toReal (hfin _)] at this
    exact ofReal_ne_top (this.trans h)
