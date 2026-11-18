/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Binary entropy

The Bernoulli measure `Ber(x, y, p)` on two distinct points has entropy `binEntropy p`, the
binary entropy function, so its zeros, its maximum `log 2` at `p = 1/2` and its monotonicity on
either side of `1/2` are facts about the entropy of any two-point law. An event is such a law:
its entropy is [the binary entropy of its probability](##InformationTheory.entropy_mem), and
given a second event its entropy [averages the binary entropies of its two conditional
probabilities](##InformationTheory.condEntropy_mem_mem).

## References

* [cover-thomas-2006]
-/

public section

open MeasureTheory ProbabilityTheory Real unitInterval

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]

/-- A Bernoulli measure on two distinct points has the binary entropy of its parameter. -/
theorem measureEntropy_bernoulliMeasure {x y : S} (h : x ≠ y) (p : I) :
    Hm[Ber(x, y, p)] = binEntropy p := by
  classical
  rw [measureEntropy_eq_sum_finset (A := {x, y})
      (bernoulliMeasure_apply_of_notMem_of_notMem p (Finset.measurableSet _).compl (by simp)
        (by simp)),
    Finset.sum_pair h, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [h, h.symm]

section event

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t : Set Ω}

/-- The entropy of an event is the binary entropy of its probability. -/
theorem entropy_mem [IsZeroOrProbabilityMeasure μ] (hs : MeasurableSet s) :
    H[(· ∈ s) ; μ] = binEntropy (μ.real s) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp
  rw [entropy_eq_sum (measurable_mem.2 hs) μ, Fintype.sum_Prop, Set.preimage_singleton_true,
    Set.preimage_singleton_false, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    ← probReal_compl_eq_one_sub hs]
  rfl

/-- The entropy of one event given another averages, over the two cases of the second, the binary
entropy of the conditional probability of the first. -/
theorem condEntropy_mem_mem [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t) :
    H[(· ∈ s) | (· ∈ t) ; μ] = μ.real t * binEntropy (μ.real (t ∩ s) / μ.real t) +
      μ.real tᶜ * binEntropy (μ.real (tᶜ ∩ s) / μ.real tᶜ) := by
  rw [condEntropy_eq_sum _ (measurable_mem.2 ht) μ, Fintype.sum_Prop, Set.preimage_singleton_true,
    Set.preimage_singleton_false, entropy_mem hs, entropy_mem hs]
  change μ.real t * binEntropy (μ[|t].real s) + μ.real tᶜ * binEntropy (μ[|tᶜ].real s) = _
  rw [cond_real_apply _ ht, cond_real_apply _ ht.compl]

/-- An event inside another has, given the larger one, the binary entropy of the ratio of their
probabilities, weighted by the probability of the larger. -/
theorem condEntropy_mem_mem_of_subset [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) :
    H[(· ∈ s) | (· ∈ t) ; μ] = μ.real t * binEntropy (μ.real s / μ.real t) := by
  rw [condEntropy_mem_mem hs ht, Set.inter_eq_self_of_subset_right hst,
    (Set.disjoint_compl_left_iff_subset.2 hst).inter_eq]
  simp

end event

end InformationTheory
