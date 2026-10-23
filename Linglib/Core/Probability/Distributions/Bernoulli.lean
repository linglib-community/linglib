/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Variance

/-!
# Bernoulli distribution: bind, variance, posterior

Binding a kernel through `Ber(x, y, p)` is the `p`-mixture of its two values, and the variance of
a real observable under `Ber(x, y, p)` is `p * (1 - p) * (f x - f y) ^ 2`. Conditioning on an
observation that both points emit with positive likelihood, the posterior mass of a point is
strictly increasing in its Bernoulli prior.

## Main results

* `ProbabilityTheory.bernoulliMeasure_bind`: `Ber(x, y, p).bind f = p • f x + (1 - p) • f y`.
* `ProbabilityTheory.variance_bernoulliMeasure`:
  `Var[f; Ber(x, y, p)] = p * (1 - p) * (f x - f y) ^ 2`.
* `ProbabilityTheory.strictMono_posterior_bernoulliMeasure`:
  `StrictMono fun p : I ↦ ((κ†Ber(x, y, p)) u).real {x}`.

[UPSTREAM] candidates for `Mathlib.Probability.Distributions.Bernoulli` and
`Mathlib.Probability.Kernel.Posterior`.
-/

@[expose] public section

open MeasureTheory unitInterval

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass X]
  (x y : X) (p : I)

theorem bernoulliMeasure_bind {f : X → Measure Y} (hf : Measurable f) :
    Ber(x, y, p).bind f = toNNReal p • f x + toNNReal (σ p) • f y := by
  ext s hs
  simp [bernoulliMeasure_def, Measure.bind_apply hs hf.aemeasurable, lintegral_add_measure,
    lintegral_smul_measure]

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

end ProbabilityTheory
