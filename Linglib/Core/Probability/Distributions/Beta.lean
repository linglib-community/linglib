/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Distributions.Beta

/-!
# Moments of the beta distribution

This file computes the mixed moments `∫ x ^ k (1 - x) ^ l` of the beta distribution with shape
parameters `a` and `b`. Tilting the beta density by `x ^ k (1 - x) ^ l` gives the beta density
with parameters `a + k` and `b + l` up to a constant, so the moment is a ratio of beta functions,
and in rising factorials `(a)_k (b)_l / (a + b)_{k + l}`.

## Main statements

* `ProbabilityTheory.ae_mem_Ioo_betaMeasure`: the beta distribution lives on `(0, 1)`.
* `ProbabilityTheory.lintegral_pow_mul_one_sub_pow_betaMeasure`: the mixed moments.

[UPSTREAM] candidate for `Mathlib.Probability.Distributions.Beta`.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {a b : ℝ}

@[fun_prop]
theorem measurable_betaPDF (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

instance (a b : ℝ) : SFinite (betaMeasure a b) := by
  rw [betaMeasure]
  infer_instance

theorem ae_mem_Ioo_betaMeasure (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo 0 1 := by
  rw [betaMeasure, ae_withDensity_iff (measurable_betaPDF a b)]
  refine ae_of_all _ fun x hx ↦ ⟨not_le.1 fun h ↦ hx ?_, not_le.1 fun h ↦ hx ?_⟩
  · exact betaPDF_eq_zero_of_nonpos h
  · exact betaPDF_eq_zero_of_one_le h

/-- The ratio of beta functions in rising factorials. -/
theorem beta_add_nat_div_beta (ha : 0 < a) (hb : 0 < b) (k l : ℕ) :
    beta (a + k) (b + l) / beta a b =
      (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ l).eval b /
        (ascPochhammer ℝ (k + l)).eval (a + b) := by
  have hne {x : ℝ} (hx : 0 < x) (j : ℕ) : x ≠ -j := ((neg_nonpos.2 j.cast_nonneg).trans_lt hx).ne'
  have hΓ {x : ℝ} (hx : 0 < x) : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  rw [← Real.Gamma_add_nat_div_Gamma_eq _ (hne ha), ← Real.Gamma_add_nat_div_Gamma_eq _ (hne hb),
    ← Real.Gamma_add_nat_div_Gamma_eq _ (hne (add_pos ha hb)), beta, beta]
  have h₁ := hΓ ha
  have h₂ := hΓ hb
  have h₃ := hΓ (add_pos ha hb)
  have h₄ := hΓ (add_pos (add_pos ha hb) (by positivity : (0 : ℝ) < k + l + 1))
  have h₅ : a + k + (b + l) = a + b + ((k + l : ℕ) : ℝ) := by push_cast; ring
  rw [h₅]
  field_simp

/-- The mixed moments of the beta distribution. -/
theorem lintegral_pow_mul_one_sub_pow_betaMeasure (ha : 0 < a) (hb : 0 < b) (k l : ℕ) :
    ∫⁻ x, ENNReal.ofReal x ^ k * ENNReal.ofReal (1 - x) ^ l ∂betaMeasure a b =
      ENNReal.ofReal ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ l).eval b /
        (ascPochhammer ℝ (k + l)).eval (a + b)) := by
  have hak : 0 < a + k := by positivity
  have hbl : 0 < b + l := by positivity
  rw [← beta_add_nat_div_beta ha hb, betaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_betaPDF a b) (by fun_prop)]
  calc ∫⁻ x, (betaPDF a b * fun x ↦ ENNReal.ofReal x ^ k * ENNReal.ofReal (1 - x) ^ l) x
      = ∫⁻ x, ENNReal.ofReal (beta (a + k) (b + l) / beta a b) * betaPDF (a + k) (b + l) x :=
        lintegral_congr fun x ↦ ?_
    _ = _ := by
      rw [lintegral_const_mul _ (measurable_betaPDF _ _),
        lintegral_betaPDF_eq_one hak hbl, mul_one]
  by_cases hx : x ∈ Ioo 0 1
  · obtain ⟨hx₀, hx₁⟩ := hx
    simp only [Pi.mul_apply]
    rw [betaPDF_of_pos_lt_one hx₀ hx₁, betaPDF_of_pos_lt_one hx₀ hx₁,
      ← ENNReal.ofReal_pow hx₀.le, ← ENNReal.ofReal_pow (sub_nonneg.2 hx₁.le),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by have := beta_pos ha hb; positivity),
      ← ENNReal.ofReal_mul (div_nonneg (beta_pos hak hbl).le (beta_pos ha hb).le)]
    congr 1
    have hk : x ^ (a + k - 1) = x ^ (a - 1) * x ^ k := by
      rw [show a + k - 1 = a - 1 + k by ring, Real.rpow_add_natCast hx₀.ne']
    have hl : (1 - x) ^ (b + l - 1) = (1 - x) ^ (b - 1) * (1 - x) ^ l := by
      rw [show b + l - 1 = b - 1 + l by ring, Real.rpow_add_natCast (sub_pos.2 hx₁).ne']
    have := (beta_pos hak hbl).ne'
    have := (beta_pos ha hb).ne'
    rw [hk, hl]
    field_simp
  · have h₀ : betaPDF a b x = 0 ∧ betaPDF (a + k) (b + l) x = 0 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with hx | hx
      · exact ⟨betaPDF_eq_zero_of_nonpos hx, betaPDF_eq_zero_of_nonpos hx⟩
      · exact ⟨betaPDF_eq_zero_of_one_le hx, betaPDF_eq_zero_of_one_le hx⟩
    simp [h₀.1, h₀.2]

end ProbabilityTheory
