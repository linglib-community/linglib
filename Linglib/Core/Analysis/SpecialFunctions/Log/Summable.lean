/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Vanishing of the product of `1 - f i`

For a family with `0 ≤ f i ≤ 1`, the finite products of the `1 - f i` are at most
`exp (-∑ i ∈ s, f i)`, so they [tend to zero](##Real.hasProd_one_sub_zero_of_not_summable) when
`f` is not summable; when `f` is summable and no factor vanishes, the infinite product
[is nonzero](##tprod_one_sub_ne_zero_of_summable). The product is therefore zero
[exactly when](##Real.hasProd_one_sub_zero_iff) some factor vanishes or `f` is not summable, and
the same holds [in `ℝ≥0∞`](##ENNReal.hasProd_one_sub_zero_iff) with no hypothesis on `f`. An
antitone sequence in `ℝ≥0∞` is such a product: its decrements
[telescope](##ENNReal.tsum_sub_succ_add_iInf), and each term is the previous one times
[one minus its relative decrement](##ENNReal.mul_one_sub_sub_succ_div).

`[UPSTREAM]` candidate for `Mathlib/Analysis/SpecialFunctions/Log/Summable.lean`, with the two
transfer lemmas for `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`.
-/

public section

open Filter Finset Topology
open scoped ENNReal NNReal

variable {ι : Type*}

section NormedRing

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [NormMulClass R] [CompleteSpace R]
  {f : ι → R}

theorem tprod_one_sub_ne_zero_of_summable (hf : ∀ i, 1 - f i ≠ 0) (hu : Summable (‖f ·‖)) :
    ∏' i, (1 - f i) ≠ 0 := by
  simpa [sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable (f := fun i ↦ -f i)
    (by simpa [sub_eq_add_neg] using hf) (by simpa using hu)

end NormedRing

namespace Real

variable {f : ι → ℝ}

theorem prod_one_sub_le_exp_neg_sum (s : Finset ι) (hf : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, (1 - f i) ≤ exp (-∑ i ∈ s, f i) := by
  rw [← sum_neg_distrib, exp_sum]
  exact prod_le_prod₀ (fun i hi ↦ sub_nonneg.2 (hf i hi)) fun i _ ↦ one_sub_le_exp_neg _

theorem hasProd_one_sub_zero_of_not_summable (h₀ : ∀ i, 0 ≤ f i) (h₁ : ∀ i, f i ≤ 1)
    (hf : ¬Summable f) : HasProd (fun i ↦ 1 - f i) 0 :=
  squeeze_zero (fun _ ↦ prod_nonneg fun i _ ↦ sub_nonneg.2 (h₁ i))
    (fun s ↦ prod_one_sub_le_exp_neg_sum s fun i _ ↦ h₁ i) <|
    tendsto_exp_neg_atTop_nhds_zero.comp <|
      (tendsto_atTop_of_monotone (sum_mono_set_of_nonneg h₀)).resolve_right hf

/-- For `0 ≤ f i ≤ 1`, the product of the `1 - f i` is zero exactly when some factor vanishes or
`f` is not summable. -/
theorem hasProd_one_sub_zero_iff (h₀ : ∀ i, 0 ≤ f i) (h₁ : ∀ i, f i ≤ 1) :
    HasProd (fun i ↦ 1 - f i) 0 ↔ (∃ i, f i = 1) ∨ ¬Summable f := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra! hc
    exact tprod_one_sub_ne_zero_of_summable (fun i ↦ sub_ne_zero.2 (hc.1 i).symm)
      (by simpa [abs_of_nonneg (h₀ _)] using hc.2) h.tprod_eq
  · rintro (⟨i, hi⟩ | hf)
    · exact hasProd_zero_of_exists_eq_zero ⟨i, by simp [hi]⟩
    · exact hasProd_one_sub_zero_of_not_summable h₀ h₁ hf

end Real

namespace ENNReal

variable {f : ι → ℝ≥0∞} {a : ℝ≥0∞}

theorem hasProd_toReal_iff (hf : ∀ i, f i ≠ ∞) (ha : a ≠ ∞) :
    HasProd (fun i ↦ (f i).toReal) a.toReal ↔ HasProd f a := by
  simp_rw [HasProd, ← toReal_prod]
  exact tendsto_toReal_iff (fun s ↦ prod_ne_top fun i _ ↦ hf i) ha

/-- A product of factors at most one converges exactly when its partial products do. -/
theorem hasProd_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n ≤ 1) :
    HasProd f a ↔ Tendsto (fun n ↦ ∏ i ∈ range n, f i) atTop (𝓝 a) := by
  refine ⟨HasProd.tendsto_prod_nat, fun h ↦ ?_⟩
  have hprod := (multipliable_of_le_one hf).hasProd
  rwa [tendsto_nhds_unique hprod.tendsto_prod_nat h] at hprod

/-- The product of the `1 - f i` is zero exactly when some factor vanishes or the `f i` have
infinite sum. -/
theorem hasProd_one_sub_zero_iff :
    HasProd (fun i ↦ 1 - f i) 0 ↔ (∃ i, 1 ≤ f i) ∨ ∑' i, f i = ∞ := by
  by_cases! h : ∃ i, 1 ≤ f i
  · simpa [h] using hasProd_zero_of_exists_eq_zero (h.imp fun i ↦ tsub_eq_zero_of_le)
  lift f to ι → ℝ≥0 using fun i ↦ (h i).ne_top
  replace h i : f i < 1 := by simpa using h i
  rw [← hasProd_toReal_iff (fun i ↦ sub_ne_top one_ne_top) zero_ne_top]
  simpa [toReal_sub_of_le, (h _).le, (h _).ne, (h _).not_ge,
    tsum_coe_eq_top_iff_not_summable_coe] using Real.hasProd_one_sub_zero_iff
      (fun i ↦ (f i).coe_nonneg) fun i ↦ mod_cast (h i).le

/-! ### Antitone sequences

The decrements `s n - s (n + 1)` of an antitone sequence telescope, and each term is the previous
one times one minus its relative decrement, so the sequence is a product of such factors. -/

section Antitone

variable {s : ℕ → ℝ≥0∞}

/-- The decrements of an antitone sequence before `n` and its `n`th term sum to its first term. -/
theorem sum_range_sub_succ_add (hs : Antitone s) (n : ℕ) :
    ∑ k ∈ range n, (s k - s (k + 1)) + s n = s 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_assoc, tsub_add_cancel_of_le (hs n.le_succ), ih]

/-- The decrements of an antitone sequence and its infimum sum to its first term. -/
theorem tsum_sub_succ_add_iInf (hs : Antitone s) (h0 : s 0 ≠ ∞) :
    ∑' n, (s n - s (n + 1)) + ⨅ n, s n = s 0 := by
  have hsum (n : ℕ) : ∑ k ∈ range n, (s k - s (k + 1)) = s 0 - s n :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top h0 (hs n.zero_le)) (sum_range_sub_succ_add hs n)
  rw [ENNReal.tsum_eq_iSup_nat, iSup_congr hsum, ← ENNReal.sub_iInf,
    tsub_add_cancel_of_le (iInf_le _ 0)]

/-- A term of an antitone sequence times one minus its relative decrement is the next term. -/
theorem mul_one_sub_sub_succ_div (hs : Antitone s) (h0 : s 0 ≠ ∞) (n : ℕ) :
    s n * (1 - (s n - s (n + 1)) / s n) = s (n + 1) := by
  have hn : s n ≠ ∞ := ne_top_of_le_ne_top h0 (hs n.zero_le)
  by_cases h : s n = 0
  · rw [h, zero_mul]
    exact (nonpos_iff_eq_zero.1 ((hs n.le_succ).trans h.le)).symm
  · rw [ENNReal.mul_sub fun _ _ ↦ hn, mul_one, ENNReal.mul_div_cancel h hn,
      ENNReal.sub_sub_cancel hn (hs n.le_succ)]

end Antitone

end ENNReal
