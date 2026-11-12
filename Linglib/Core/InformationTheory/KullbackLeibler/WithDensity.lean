/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Divergence from a reweighted measure

Reweighting a reference measure `μ` by the exponential of minus a cost gives the measure
`μ.withDensity (exp (-c))`, which has no mass where the cost is infinite. For any finite measure
`q`, the expected cost under `q` and the divergence of `q` from the reference, together with the
mass of the reweighted measure, equal [the divergence of `q` from the reweighted measure together
with the mass of the reference](##InformationTheory.lintegral_add_klDiv_add_withDensity). The
identity holds between extended nonnegative reals with no condition on supports: both sides are
infinite exactly when `q` charges a set the reweighted measure does not.

So expected cost plus divergence from the reference is [least at the reweighted
measure](##InformationTheory.measure_univ_le_lintegral_add_klDiv_add_withDensity), and [only
there](##InformationTheory.lintegral_add_klDiv_add_withDensity_eq_iff), among all finite measures
and not only those of a fixed mass.

## TODO

* Prove `lintegral_add_klDiv_add_withDensity`. Where `q` is not absolutely continuous with respect
  to the reweighted measure both sides are `∞`: either `q` is not absolutely continuous with
  respect to `μ`, or it charges the set of infinite cost. Otherwise write `g` for the density of
  `q` against the reweighted measure and `w = exp (-c)`; then `q` has density `g * w` against `μ`,
  and with `klFun x = x * log x + 1 - x` the pointwise identity
  `klFun g * w + 1 = klFun (g * w) + g * w * c + w` integrates against `μ` to the statement.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

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
  sorry

/-- Expected cost plus divergence from the reference is at least the mass the reweighting
removes. -/
theorem measure_univ_le_lintegral_add_klDiv_add_withDensity (hc : Measurable c) :
    μ Set.univ ≤
      ∫⁻ x, c x ∂q + klDiv q μ + μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ :=
  lintegral_add_klDiv_add_withDensity q μ hc ▸ le_add_self

/-- Expected cost plus divergence from the reference attains that bound only at the reweighted
measure. -/
theorem lintegral_add_klDiv_add_withDensity_eq_iff (hc : Measurable c) :
    ∫⁻ x, c x ∂q + klDiv q μ + μ.withDensity (fun x ↦ EReal.exp (-(c x : EReal))) Set.univ =
        μ Set.univ ↔
      q = μ.withDensity fun x ↦ EReal.exp (-(c x : EReal)) := by
  rw [lintegral_add_klDiv_add_withDensity q μ hc, ← klDiv_eq_zero_iff]
  exact ⟨fun h ↦ (ENNReal.add_left_inj (measure_ne_top μ _)).1 (h.trans (zero_add _).symm),
    fun h ↦ by rw [h, zero_add]⟩

end InformationTheory
