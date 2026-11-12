/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.StochasticOrder
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Variance

/-!
# Bernoulli distribution: bind, variance, posterior, stochastic order

Binding a kernel through `Ber(x, y, p)` is the `p`-mixture of its two values, as is a lower
integral against it, and the variance of a real observable under `Ber(x, y, p)` is
`p * (1 - p) * (f x - f y) ^ 2`. Conditioning on an observation that both points emit with
positive likelihood, the posterior mass of a point is strictly increasing in its Bernoulli prior.

## Main results

* `ProbabilityTheory.bernoulliMeasure_bind`: `Ber(x, y, p).bind f = p • f x + (1 - p) • f y`.
* `ProbabilityTheory.lintegral_bernoulliMeasure`:
  `∫⁻ z, f z ∂Ber(x, y, p) = p * f x + (1 - p) * f y`.
* `ProbabilityTheory.variance_bernoulliMeasure`:
  `Var[f; Ber(x, y, p)] = p * (1 - p) * (f x - f y) ^ 2`.
* `ProbabilityTheory.strictMono_posterior_bernoulliMeasure`:
  `StrictMono fun p : I ↦ ((κ†Ber(x, y, p)) u).real {x}`.
* `ProbabilityTheory.bernoulliMeasure_stochasticLE`: `Ber(x, y, p) ≤ₛₜ Ber(x, y, q)` for `y ≤ x`
  and `p ≤ q`, through a monotone coupling.

[UPSTREAM] candidates for `Mathlib.Probability.Distributions.Bernoulli` and
`Mathlib.Probability.Kernel.Posterior`.
-/

public section

open MeasureTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass X]
  (x y : X) (p : I)

theorem bernoulliMeasure_bind {f : X → Measure Y} (hf : Measurable f) :
    Ber(x, y, p).bind f = toNNReal p • f x + toNNReal (σ p) • f y := by
  ext s hs
  simp [bernoulliMeasure_def, Measure.bind_apply hs hf.aemeasurable, lintegral_add_measure,
    lintegral_smul_measure]

omit [MeasurableSingletonClass X] in
/-- The law of a two-valued random variable is Bernoulli. -/
theorem map_piecewise_const_eq_bernoulliMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {s : Set Ω} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    μ.map (s.piecewise (fun _ ↦ x) fun _ ↦ y) =
      Ber(x, y, ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩) := by
  classical
  have h1 : ((toNNReal ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩ : NNReal) : ℝ≥0∞)
      = μ s :=
    (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (measure_ne_top μ _)).1
      (by simp [measureReal_def])
  have h0 : ((toNNReal (σ ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩) : NNReal) : ℝ≥0∞)
      = μ sᶜ :=
    (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (measure_ne_top μ _)).1
      (by simp [coe_symm_eq, ← measureReal_def, probReal_compl_eq_one_sub hs])
  ext t ht
  rw [Measure.map_apply (measurable_const.piecewise hs measurable_const) ht,
    bernoulliMeasure_apply _ ht, h1, h0, Set.piecewise_preimage]
  by_cases hx : x ∈ t <;> by_cases hy : y ∈ t <;> simp [hx, hy, Set.compl_eq_univ_sdiff]

theorem lintegral_bernoulliMeasure (f : X → ℝ≥0∞) :
    ∫⁻ z, f z ∂Ber(x, y, p) = toNNReal p * f x + toNNReal (σ p) * f y := by
  rw [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]

theorem variance_bernoulliMeasure {f : X → ℝ} (hf : AEMeasurable f Ber(x, y, p)) :
    Var[f; Ber(x, y, p)] = p * (1 - p) * (f x - f y) ^ 2 := by
  rw [variance_eq_integral hf]
  simp only [integral_bernoulliMeasure, smul_eq_mul]
  ring

theorem eq_or_eq_of_bernoulliMeasure_singleton_ne_zero {z : X} (hz : Ber(x, y, p) {z} ≠ 0) :
    z = x ∨ z = y := by
  contrapose! hz
  exact bernoulliMeasure_apply_of_notMem_of_notMem p (measurableSet_singleton z)
    (Set.notMem_singleton_iff.mpr hz.1.symm) (Set.notMem_singleton_iff.mpr hz.2.symm)

section Posterior

variable [Fintype X] [StandardBorelSpace X] [Nonempty X] {𝓧 : Type*} [MeasurableSpace 𝓧]
  [MeasurableSingletonClass 𝓧] (κ : Kernel X 𝓧) [IsFiniteKernel κ] {u : 𝓧}

/-- At an observation that both points emit with positive likelihood, the posterior mass of a
point is strictly increasing in its Bernoulli prior: a state that is more likely a priori is
more likely a posteriori. -/
theorem strictMono_posterior_bernoulliMeasure (hxy : x ≠ y) (hκx : κ x {u} ≠ 0)
    (hκy : κ y {u} ≠ 0) : StrictMono fun p : I ↦ ((κ†Ber(x, y, p)) u).real {x} := by
  intro p q hpq
  refine posterior_real_singleton_lt_posterior_of_pair κ Ber(x, y, p) hxy
    (fun z ↦ eq_or_eq_of_bernoulliMeasure_singleton_ne_zero x y p)
    (fun z ↦ eq_or_eq_of_bernoulliMeasure_singleton_ne_zero x y q) hκx hκy ?_
  simpa [hxy.symm] using hpq

end Posterior

section StochasticOrder

open MeasureTheory.Measure

variable [Preorder X] {x y} {p} {q : I}

/-- Bernoulli measures on a pair `y ≤ x` are coupled monotonically in the weight of the upper
point: the coupling moves the extra mass `q - p` from `y` up to `x`. -/
theorem exists_isMonotoneCoupling_bernoulliMeasure (hyx : y ≤ x) (hpq : p ≤ q) :
    ∃ γ, IsMonotoneCoupling γ Ber(x, y, p) Ber(x, y, q) := by
  have hpq' : toNNReal p ≤ toNNReal q := hpq
  have hq : toNNReal (σ q) = 1 - toNNReal q := eq_tsub_of_add_eq (toNNReal_symm_add_toNNReal q)
  have hp : toNNReal (σ p) = 1 - toNNReal p := eq_tsub_of_add_eq (toNNReal_symm_add_toNNReal p)
  have hq1 : toNNReal q ≤ 1 := q.2.2
  refine ⟨toNNReal p • dirac (x, x) + ((toNNReal q - toNNReal p) • dirac (y, x)
    + toNNReal (σ q) • dirac (y, y)), ?_, ?_, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, map_dirac' measurable_fst,
      map_dirac' measurable_fst, map_dirac' measurable_fst, ← add_smul, hq, add_comm (_ - _),
      tsub_add_tsub_cancel hq1 hpq', bernoulliMeasure_def, hp]
    all_goals fun_prop
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, map_dirac' measurable_snd,
      map_dirac' measurable_snd, map_dirac' measurable_snd, ← add_assoc, ← add_smul,
      add_tsub_cancel_of_le hpq', bernoulliMeasure_def]
    all_goals fun_prop
  · have key : ∀ a b : X, a ≤ b → ∀ᵐ z ∂dirac (a, b), z.1 ≤ z.2 := fun a b h ↦ by
      simpa [ae_dirac_eq] using h
    exact ae_add_measure_iff.2 ⟨ae_smul_measure (key x x le_rfl) _, ae_add_measure_iff.2
      ⟨ae_smul_measure (key y x hyx) _, ae_smul_measure (key y y le_rfl) _⟩⟩

/-- The Bernoulli measure on a pair `y ≤ x` is stochastically increasing in the weight of `x`. -/
theorem bernoulliMeasure_stochasticLE (hyx : y ≤ x) (hpq : p ≤ q) : Ber(x, y, p) ≤ₛₜ Ber(x, y, q) :=
  let ⟨_, hγ⟩ := exists_isMonotoneCoupling_bernoulliMeasure hyx hpq
  hγ.stochasticLE

end StochasticOrder

end ProbabilityTheory
