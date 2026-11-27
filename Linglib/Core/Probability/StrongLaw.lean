/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable.Basic
public import Mathlib.Probability.StrongLaw

/-!
# The strong law of large numbers on a product space

Under the law `Measure.infinitePi fun _ ↦ ν` of a sequence of independent random variables with
law `ν`, the averages of an integrable function along the sequence converge almost surely to its
integral against `ν`. The coordinates are independent, and they are identically distributed
because they are exchangeable.

## Main results

* `ProbabilityTheory.ae_tendsto_average_infinitePi`: the strong law for the coordinates of a
  product of copies of one probability measure.

`[UPSTREAM]` candidate for `Mathlib/Probability/StrongLaw.lean`.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

/-- Under the law of a sequence of independent random variables with law `ν`, the averages of an
integrable function along the sequence converge almost surely to its integral against `ν`. -/
theorem ae_tendsto_average_infinitePi {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] {f : E → ℝ} (hf : Measurable f) (hint : Integrable f ν) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ ↦ ν),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (x i)) atTop
        (𝓝 (∫ a, f a ∂ν)) := by
  set P := Measure.infinitePi fun _ : ℕ ↦ ν
  have hex : Exchangeable (fun i (x : ℕ → E) ↦ x i) P := exchangeable_eval_iff.2 inferInstance
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ ↦ ν) fun _ ↦ hf
  have h0 : P.map (fun x ↦ x 0) = ν := Measure.infinitePi_map_eval _ 0
  have hint0 : Integrable (fun x : ℕ → E ↦ f (x 0)) P :=
    (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply 0).aemeasurable).1
      (h0 ▸ hint)
  have := strong_law_ae (fun i (x : ℕ → E) ↦ f (x i)) hint0 (fun i j hij ↦ hind.indepFun hij)
    fun i ↦ (hex.comp hf).identDistrib i 0
  rwa [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable, h0] at this

end ProbabilityTheory
