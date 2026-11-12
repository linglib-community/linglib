/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Divergence from a reweighted measure

Reweighting a reference measure `μ` by the exponential of minus a cost gives the measure
`μ.withDensity (exp (-c))`, which has no mass where the cost is infinite. For any finite measure
`q`, the expected cost under `q` and the divergence of `q` from the reference, together with the
mass of the reweighted measure, equal [the divergence of `q` from the reweighted measure together
with the mass of the reference](##InformationTheory.lintegral_add_klDiv_add_withDensity). The
identity holds between extended nonnegative reals with no condition on supports or integrability:
each side is an integral of a nonnegative function, and both are infinite in particular whenever
`q` charges a set the reweighted measure does not.

For probability measures the reweighted measure may be normalized, and the two masses become the
negative logarithm of its mass: expected cost plus divergence from the reference is the divergence
from the normalized measure [plus that
constant](##InformationTheory.lintegral_add_klDiv_eq_klDiv_cond_add). So it is [at least the
constant](##InformationTheory.toENNReal_neg_log_le_lintegral_add_klDiv), and [only the normalized
measure attains it](##InformationTheory.lintegral_add_klDiv_eq_iff). The normalized measure is a
row of `ProbabilityTheory.Kernel.ofDensity`.

## TODO

* The form for a mixture of measures against one decoder.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

open Real in
private theorem klFun_exp_neg_mul (r s : ℝ) (hs : 0 ≤ s) :
    r * (exp (-r) * s) + klFun (exp (-r) * s) + exp (-r) = exp (-r) * klFun s + 1 := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [klFun]; ring
  · simp only [klFun]
    rw [Real.log_mul (exp_pos _).ne' hs.ne', Real.log_exp]
    ring

open Real in
private theorem ofReal_klFun_exp_neg_mul (c g : ℝ≥0∞) (hg : EReal.exp (-(c : EReal)) ≠ 0 → g < ∞) :
    c * (EReal.exp (-(c : EReal)) * g) +
        ENNReal.ofReal (klFun (EReal.exp (-(c : EReal)) * g).toReal) + EReal.exp (-(c : EReal)) =
      EReal.exp (-(c : EReal)) * ENNReal.ofReal (klFun g.toReal) + 1 := by
  induction c with
  | top => simp [klFun_zero]
  | coe r =>
    have hw : EReal.exp (-((r : ℝ≥0∞) : EReal)) = ENNReal.ofReal (exp (-(r : ℝ))) := by
      rw [← EReal.exp_coe]; rfl
    rw [hw] at hg ⊢
    lift g to NNReal using (hg (by positivity)).ne
    have h := klFun_exp_neg_mul r g g.2
    have e1 : (r : ℝ≥0∞) = ENNReal.ofReal r := by simp
    have e2 : (g : ℝ≥0∞) = ENNReal.ofReal g := by simp
    rw [e1, e2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      ← ENNReal.ofReal_add (by positivity) (klFun_nonneg (by positivity)),
      ← ENNReal.ofReal_add (add_nonneg (by positivity)
        (klFun_nonneg (x := exp (-(r : ℝ)) * g) (by positivity))) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), h,
      ENNReal.ofReal_add ?_ zero_le_one, ENNReal.ofReal_one]
    exact mul_nonneg (exp_pos _).le (klFun_nonneg g.2)

variable {β : Type*} [MeasurableSpace β] {c : β → ℝ≥0∞} (q μ : Measure β) [IsFiniteMeasure q]
  [IsFiniteMeasure μ]

instance : IsFiniteMeasure (μ.withDensity fun x ↦ EReal.exp (-(c x : EReal))) :=
  isFiniteMeasure_withDensity (((lintegral_mono fun x ↦ by
    rw [EReal.exp_le_one_iff, EReal.neg_le, neg_zero]
    exact EReal.coe_ennreal_nonneg _).trans_eq lintegral_one).trans_lt (measure_lt_top μ _)).ne

/-- The expected cost under `q`, the divergence of `q` from the reference `μ` and the mass of the
reference reweighted by `exp (-c)` add up to the divergence of `q` from the reweighted measure and
the mass of the reference. -/
theorem lintegral_add_klDiv_add_withDensity (hc : Measurable c) :
    ∫⁻ x, c x ∂q + klDiv q μ + μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ =
      klDiv q (μ.withDensity fun x ↦ EReal.exp (-(c x : EReal))) + μ Set.univ := by
  set w : β → ℝ≥0∞ := fun x ↦ EReal.exp (-(c x : EReal)) with hw_def
  have hw : Measurable w := EReal.measurable_exp.comp hc.coe_ereal_ennreal.neg
  by_cases hq : q ≪ μ.withDensity w
  · have hqμ : q ≪ μ := hq.trans (withDensity_absolutelyContinuous μ w)
    set g := q.rnDeriv (μ.withDensity w) with hg_def
    have hg : Measurable g := Measure.measurable_rnDeriv _ _
    have hf : q.rnDeriv μ =ᵐ[μ] w * g := by
      have h1 : q = μ.withDensity (w * g) := by
        rw [withDensity_mul μ hw hg, Measure.withDensity_rnDeriv_eq q _ hq]
      conv_lhs => rw [h1]
      exact Measure.rnDeriv_withDensity μ (hw.mul hg)
    have hfin : ∀ᵐ x ∂μ, w x ≠ 0 → g x < ∞ :=
      (ae_withDensity_iff hw).1 (Measure.rnDeriv_lt_top q _)
    rw [klDiv_eq_lintegral_klFun_of_ac hq, klDiv_eq_lintegral_klFun_of_ac hqμ,
      ← lintegral_rnDeriv_mul hqμ hc.aemeasurable, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, lintegral_withDensity_eq_lintegral_mul μ hw (by fun_prop),
      ← lintegral_one (μ := μ), ← lintegral_add_left (by fun_prop),
      ← lintegral_add_left (by fun_prop), ← lintegral_add_left (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [hf, hfin] with x hx hx'
    simp only [hx, Pi.mul_apply]
    rw [mul_comm (w x * g x) (c x)]
    exact ofReal_klFun_exp_neg_mul (c x) (g x) hx'
  · rw [klDiv_of_not_ac hq, top_add]
    by_cases hqμ : q ≪ μ
    swap; · simp [klDiv_of_not_ac hqμ]
    have hc_top : q {x | c x = ∞} ≠ 0 := by
      intro h0
      refine hq (Measure.AbsolutelyContinuous.mk fun s hs hμs ↦ ?_)
      rw [withDensity_apply_eq_zero' hw.aemeasurable] at hμs
      have := hqμ hμs
      refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null this h0)
      by_cases hx' : c x = ∞
      · exact Or.inr hx'
      · refine Or.inl ⟨?_, hx⟩
        simp only [Set.mem_ofPred_eq, hw_def, ne_eq, EReal.exp_eq_zero_iff]
        lift c x to NNReal using hx' with r
        exact (EReal.coe_ne_bot (-(r : ℝ)))
    have : ∫⁻ x, c x ∂q = ∞ := by
      refine top_unique ?_
      calc ∞ = ∫⁻ x in {x | c x = ∞}, ∞ ∂q := by
            rw [setLIntegral_const, ENNReal.top_mul hc_top]
        _ = ∫⁻ x in {x | c x = ∞}, c x ∂q :=
            (setLIntegral_congr_fun (hc (measurableSet_singleton _)) fun x hx ↦ hx.symm)
        _ ≤ ∫⁻ x, c x ∂q := setLIntegral_le_lintegral _ _
    simp [this]

/-! ### Probability measures -/

section Probability

variable [IsProbabilityMeasure q] [IsProbabilityMeasure μ]

/-- For probability measures, the expected cost under `q` plus the divergence of `q` from the
reference is the divergence of `q` from the normalized reweighted measure plus the negative
logarithm of the mass of the reweighted measure. -/
theorem lintegral_add_klDiv_eq_klDiv_cond_add (hc : Measurable c) :
    ∫⁻ x, c x ∂q + klDiv q μ =
      klDiv q (μ.withDensity fun x ↦ EReal.exp (-(c x : EReal)))[|Set.univ] +
        (-ENNReal.log (μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ)).toENNReal := by
  have h1 := lintegral_add_klDiv_add_withDensity q μ hc
  set ρ := μ.withDensity fun x ↦ EReal.exp (-(c x : EReal)) with hρ
  rcases eq_or_ne (ρ Set.univ) 0 with hZ | hZ
  · rw [hZ, ENNReal.log_zero, EReal.neg_bot, EReal.toENNReal_top, add_top]
    rw [hZ, add_zero, Measure.measure_univ_eq_zero.1 hZ, klDiv_zero_right, top_add] at h1
    exact h1
  · have hZtop : ρ Set.univ ≠ ∞ := measure_ne_top ρ _
    have hZle : ρ Set.univ ≤ 1 := by
      rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine (lintegral_mono fun x ↦ ?_).trans_eq (lintegral_one.trans measure_univ)
      rw [EReal.exp_le_one_iff, EReal.neg_le, neg_zero]
      exact EReal.coe_ennreal_nonneg _
    have : IsProbabilityMeasure ρ[|Set.univ] := cond_isProbabilityMeasure_of_finite hZ hZtop
    have hk : EReal.exp (-(((-ENNReal.log (ρ Set.univ)).toENNReal : ℝ≥0∞) : EReal)) =
        ρ Set.univ := by
      rw [EReal.coe_toENNReal (EReal.neg_nonneg.2 (ENNReal.log_le_zero_iff.2 hZle)), neg_neg,
        ENNReal.exp_log]
    have hρ' : (ρ[|Set.univ]).withDensity (fun _ ↦ ρ Set.univ) = ρ := by
      rw [withDensity_const, ProbabilityTheory.cond, Measure.restrict_univ, smul_smul,
        ENNReal.mul_inv_cancel hZ hZtop, one_smul]
    have h2 := lintegral_add_klDiv_add_withDensity q ρ[|Set.univ]
      (measurable_const (a := (-ENNReal.log (ρ Set.univ)).toENNReal))
    simp only [hk, hρ', lintegral_const, measure_univ, mul_one] at h2
    rw [measure_univ (μ := μ)] at h1
    rw [← ENNReal.add_left_inj hZtop, h1, ← h2]
    ring

/-- For probability measures, expected cost plus divergence from the reference is at least the
negative logarithm of the mass of the reweighted measure. -/
theorem toENNReal_neg_log_le_lintegral_add_klDiv (hc : Measurable c) :
    (-ENNReal.log (μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ)).toENNReal ≤
      ∫⁻ x, c x ∂q + klDiv q μ :=
  lintegral_add_klDiv_eq_klDiv_cond_add q μ hc ▸ le_add_self

/-- For probability measures, expected cost plus divergence from the reference attains that bound
only at the normalized reweighted measure, when the reweighted measure is not zero. -/
theorem lintegral_add_klDiv_eq_iff (hc : Measurable c)
    (h : μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ ≠ 0) :
    ∫⁻ x, c x ∂q + klDiv q μ =
        (-ENNReal.log (μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ)).toENNReal ↔
      q = (μ.withDensity fun x ↦ EReal.exp (-(c x : EReal)))[|Set.univ] := by
  have htop : (-ENNReal.log (μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal)))
      Set.univ)).toENNReal ≠ ∞ := by
    rw [ne_eq, EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff, ENNReal.log_eq_bot_iff]
    exact h
  rw [lintegral_add_klDiv_eq_klDiv_cond_add q μ hc, ← klDiv_eq_zero_iff]
  exact ⟨fun h0 ↦ (ENNReal.add_left_inj htop).1 (h0.trans (zero_add _).symm),
    fun h0 ↦ by rw [h0, zero_add]⟩

end Probability

end InformationTheory
