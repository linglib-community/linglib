/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Measure
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Entropy of a Bernoulli measure

The Bernoulli measure `Ber(x, y, p)` on two distinct points has entropy `binEntropy p`, the
binary entropy function. Its zeros, its maximum `log 2` at `p = 1/2` and its monotonicity on
either side of `1/2` are therefore facts about the entropy of any two-point law.

## Main statements

* `measureEntropy_bernoulliMeasure`: `Hm[Ber(x, y, p)] = binEntropy p` for `x ≠ y`.

## References

* [cover-thomas-2006]
-/

@[expose] public section

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

end InformationTheory
