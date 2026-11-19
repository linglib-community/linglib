/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Kullback–Leibler divergence from a tilted measure

For probability measures `q` and `μ` and a function `f`, the divergence of `q` from the tilted
measure `μ.tilted f` [is](##InformationTheory.toReal_klDiv_tilted_right)
`KL(q ‖ μ) - ∫ f ∂q + log ∫ exp f ∂μ`. Since a divergence is nonnegative and vanishes only
between equal measures, `∫ f ∂q - KL(q ‖ μ)`
[is at most](##InformationTheory.integral_sub_toReal_klDiv_le_log_integral_exp)
`log ∫ exp f ∂μ`, with equality
[exactly at](##InformationTheory.integral_sub_toReal_klDiv_eq_log_integral_exp_iff)
`μ.tilted f`. This is the Gibbs variational principle. Read as a lower bound on the divergence it
is the Donsker–Varadhan inequality, which
[holds](##InformationTheory.ofReal_integral_sub_log_integral_exp_le_klDiv) in `ℝ≥0∞` with no
condition relating `q` to `μ`.

Suppose `f` has the same integral against `q` as against `μ.tilted f`. Then the divergences
[add](##InformationTheory.klDiv_eq_klDiv_tilted_add):
`KL(q ‖ μ) = KL(q ‖ μ.tilted f) + KL(μ.tilted f ‖ μ)`. This is the Pythagorean identity for the
tilted measure. It follows that `μ.tilted f` [is the closest
measure](##InformationTheory.klDiv_tilted_left_self_le) to `μ` among those with that integral.

`[UPSTREAM]` candidate for `Mathlib/InformationTheory/KullbackLeibler/Tilted.lean`: the module
docstring of `Mathlib/MeasureTheory/Measure/Tilted.lean` names variational expressions for the
divergence as a use of tilting by a general function.

## Implementation notes

The statements with `toReal` assume `q ≪ μ` and the integrability of `llr q μ`, as the
`toReal_klDiv` lemmas of mathlib do, since `toReal` reads an infinite divergence as `0`. `μ` is
a probability measure because the divergence from a finite measure carries the correction
`μ.real univ - q.real univ`; `MeasureTheory.integral_llr_tilted_right` is the statement for a
σ-finite `μ`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ q : Measure α} {f : α → ℝ}

namespace MeasureTheory

/-- The log-likelihood ratio of a tilted measure to its base measure is integrable against the
tilted measure as soon as the tilting function is. -/
theorem integrable_llr_tilted_left_self [SigmaFinite μ] (hf : Integrable f (μ.tilted f))
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    Integrable (llr (μ.tilted f) μ) (μ.tilted f) :=
  (integrable_congr ((tilted_absolutelyContinuous μ f).ae_le
    (log_rnDeriv_tilted_left_self h_exp))).2 (hf.sub (integrable_const _))

/-- Tilting the reference measure does not change whether the log-likelihood ratio is
integrable. -/
theorem integrable_llr_tilted_right_iff [IsFiniteMeasure q] [SigmaFinite μ] (hqμ : q ≪ μ)
    (hf : Integrable f q) (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    Integrable (llr q (μ.tilted f)) q ↔ Integrable (llr q μ) q := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrable_llr_tilted_right hqμ hf h h_exp⟩
  refine (h.sub (hf.neg.add (integrable_const (log (∫ x, exp (f x) ∂μ))))).congr ?_
  filter_upwards [llr_tilted_right hqμ h_exp] with x hx
  simp [hx]

end MeasureTheory

namespace InformationTheory

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure q]

/-- Tilting the reference measure does not change whether the divergence is finite. -/
theorem klDiv_tilted_right_ne_top_iff (hf : Integrable f q)
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) : klDiv q (μ.tilted f) ≠ ∞ ↔ klDiv q μ ≠ ∞ := by
  rw [klDiv_ne_top_iff, klDiv_ne_top_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hqμ := h.1.trans (tilted_absolutelyContinuous μ f)
    exact ⟨hqμ, (integrable_llr_tilted_right_iff hqμ hf h_exp).1 h.2⟩
  · exact ⟨h.1.trans (absolutelyContinuous_tilted h_exp),
      (integrable_llr_tilted_right_iff h.1 hf h_exp).2 h.2⟩

/-- The divergence from a tilted measure is
`KL(q ‖ μ.tilted f) = KL(q ‖ μ) - ∫ f ∂q + log ∫ exp f ∂μ`. -/
theorem toReal_klDiv_tilted_right (hqμ : q ≪ μ) (h_int : Integrable (llr q μ) q)
    (hf : Integrable f q) (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    (klDiv q (μ.tilted f)).toReal =
      (klDiv q μ).toReal - ∫ x, f x ∂q + log (∫ x, exp (f x) ∂μ) := by
  have := isProbabilityMeasure_tilted h_exp
  rw [toReal_klDiv_of_measure_eq (hqμ.trans (absolutelyContinuous_tilted h_exp)) (by simp),
    toReal_klDiv_of_measure_eq hqμ (by simp), integral_llr_tilted_right hqμ hf h_exp h_int]

omit [IsProbabilityMeasure q] in
/-- The divergence of a tilted measure from its base measure is
`KL(μ.tilted f ‖ μ) = ∫ f ∂(μ.tilted f) - log ∫ exp f ∂μ`. -/
theorem toReal_klDiv_tilted_left_self (hf : Integrable f (μ.tilted f))
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    (klDiv (μ.tilted f) μ).toReal = ∫ x, f x ∂(μ.tilted f) - log (∫ x, exp (f x) ∂μ) := by
  have := isProbabilityMeasure_tilted h_exp
  have h := toReal_klDiv_tilted_right (tilted_absolutelyContinuous μ f)
    (integrable_llr_tilted_left_self hf h_exp) hf h_exp
  rw [klDiv_self, ENNReal.toReal_zero] at h
  linarith

/-- **Gibbs variational principle**: `∫ f ∂q - KL(q ‖ μ)` is at most `log ∫ exp f ∂μ`. -/
theorem integral_sub_toReal_klDiv_le_log_integral_exp (hqμ : q ≪ μ)
    (h_int : Integrable (llr q μ) q) (hf : Integrable f q)
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    ∫ x, f x ∂q - (klDiv q μ).toReal ≤ log (∫ x, exp (f x) ∂μ) := by
  linarith [toReal_klDiv_tilted_right hqμ h_int hf h_exp,
    ENNReal.toReal_nonneg (a := klDiv q (μ.tilted f))]

/-- `∫ f ∂q - KL(q ‖ μ)` is `log ∫ exp f ∂μ` exactly when `q` is the tilted measure. -/
theorem integral_sub_toReal_klDiv_eq_log_integral_exp_iff (hqμ : q ≪ μ)
    (h_int : Integrable (llr q μ) q) (hf : Integrable f q)
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    ∫ x, f x ∂q - (klDiv q μ).toReal = log (∫ x, exp (f x) ∂μ) ↔ q = μ.tilted f := by
  have := isProbabilityMeasure_tilted h_exp
  have hne := (klDiv_tilted_right_ne_top_iff hf h_exp).2 (klDiv_ne_top hqμ h_int)
  rw [← klDiv_eq_zero_iff, ← (ENNReal.toReal_eq_zero_iff _).trans (or_iff_left hne),
    toReal_klDiv_tilted_right hqμ h_int hf h_exp]
  constructor <;> intro h <;> linarith

omit [IsProbabilityMeasure q] in
/-- The divergence of a tilted measure from its base measure is finite. -/
theorem klDiv_tilted_left_self_ne_top (hf : Integrable f (μ.tilted f))
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) : klDiv (μ.tilted f) μ ≠ ∞ :=
  klDiv_ne_top (tilted_absolutelyContinuous μ f) (integrable_llr_tilted_left_self hf h_exp)

/-- **Pythagorean identity**: if `∫ f ∂q = ∫ f ∂(μ.tilted f)`, then
`KL(q ‖ μ) = KL(q ‖ μ.tilted f) + KL(μ.tilted f ‖ μ)`. -/
theorem klDiv_eq_klDiv_tilted_add (hf : Integrable f q) (hf' : Integrable f (μ.tilted f))
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) (h : ∫ x, f x ∂q = ∫ x, f x ∂μ.tilted f) :
    klDiv q μ = klDiv q (μ.tilted f) + klDiv (μ.tilted f) μ := by
  by_cases htop : klDiv q μ = ∞
  · rw [htop, not_not.1 (mt (klDiv_tilted_right_ne_top_iff hf h_exp).1 (not_not.2 htop)),
      top_add]
  have htop' := (klDiv_tilted_right_ne_top_iff hf h_exp).2 htop
  have hl := klDiv_tilted_left_self_ne_top hf' h_exp
  obtain ⟨hqμ, h_int⟩ := klDiv_ne_top_iff.1 htop
  rw [← ENNReal.toReal_eq_toReal_iff' htop (ENNReal.add_ne_top.2 ⟨htop', hl⟩),
    ENNReal.toReal_add htop' hl, toReal_klDiv_tilted_right hqμ h_int hf h_exp,
    toReal_klDiv_tilted_left_self hf' h_exp, h]
  ring

/-- If `∫ f ∂q = ∫ f ∂(μ.tilted f)`, then `μ.tilted f` is at least as close to `μ` as `q` is. -/
theorem klDiv_tilted_left_self_le (hf : Integrable f q) (hf' : Integrable f (μ.tilted f))
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) (h : ∫ x, f x ∂q = ∫ x, f x ∂μ.tilted f) :
    klDiv (μ.tilted f) μ ≤ klDiv q μ :=
  klDiv_eq_klDiv_tilted_add hf hf' h_exp h ▸ le_add_self

/-- **Donsker–Varadhan inequality**: the divergence of `q` from `μ` is at least
`∫ f ∂q - log ∫ exp f ∂μ`, for every `f` integrable against `q` with `exp ∘ f` integrable against
`μ`. -/
theorem ofReal_integral_sub_log_integral_exp_le_klDiv (hf : Integrable f q)
    (h_exp : Integrable (fun x ↦ exp (f x)) μ) :
    ENNReal.ofReal (∫ x, f x ∂q - log (∫ x, exp (f x) ∂μ)) ≤ klDiv q μ := by
  by_cases hqμ : q ≪ μ
  swap; · simp [hqμ]
  by_cases h_int : Integrable (llr q μ) q
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top hqμ h_int)]
  exact ENNReal.ofReal_le_ofReal
    (by linarith [integral_sub_toReal_klDiv_le_log_integral_exp hqμ h_int hf h_exp])

end InformationTheory
