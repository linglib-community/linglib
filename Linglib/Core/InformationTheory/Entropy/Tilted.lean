/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Measure
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.Tilted

/-!
# The Gibbs measure has the greatest entropy at its mean

On a finite type, the counting measure tilted by a score gives each point mass proportional to
the exponential of its score. For any probability measure, its entropy, its expected score and
its divergence from the tilted measure [add up to the logarithm of the
normalizer](##InformationTheory.toReal_klDiv_count_tilted_add_measureEntropy). A measure with the
same expected score as the tilted measure therefore has [no more
entropy](##InformationTheory.measureEntropy_le_count_tilted), and has as much [only if it is the
tilted measure](##InformationTheory.measureEntropy_eq_count_tilted_iff): among the distributions
that agree on the average score, the exponential one assumes the least.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [Nonempty S]
  (f : S → ℝ) (q : Measure S) [IsProbabilityMeasure q]

instance : IsProbabilityMeasure (Measure.count.tilted f) := isProbabilityMeasure_tilted .of_finite

omit [IsProbabilityMeasure q] in
theorem absolutelyContinuous_count_tilted : q ≪ Measure.count.tilted f :=
  Measure.absolutelyContinuous_of_forall_singleton fun s hs ↦ absurd hs <|
    (measureReal_ne_zero_iff (measure_ne_top _ _)).1 <| by
      rw [count_tilted_real_singleton]
      exact (softmax_pos f s).ne'

/-- The divergence of a probability measure from the tilted counting measure and its entropy add
up to the logarithm of the normalizer less its expected score. -/
theorem toReal_klDiv_count_tilted_add_measureEntropy :
    (klDiv q (Measure.count.tilted f)).toReal + Hm[q] =
      log (∑ s, exp (f s)) - ∫ s, f s ∂q := by
  rw [toReal_klDiv_add_measureEntropy (absolutelyContinuous_count_tilted f q),
    integral_fintype .of_finite]
  simp_rw [count_tilted_real_singleton, log_softmax, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul, smul_eq_mul, neg_sub]

variable {f q}

/-- A probability measure with the expected score of the tilted counting measure has no more
entropy than it. -/
theorem measureEntropy_le_count_tilted
    (h : ∫ s, f s ∂q = ∫ s, f s ∂(Measure.count.tilted f)) :
    Hm[q] ≤ Hm[Measure.count.tilted f] := by
  have h1 := toReal_klDiv_count_tilted_add_measureEntropy f q
  have h2 := toReal_klDiv_count_tilted_add_measureEntropy f (Measure.count.tilted f)
  rw [klDiv_self, ENNReal.toReal_zero, zero_add] at h2
  linarith [ENNReal.toReal_nonneg (a := klDiv q (Measure.count.tilted f))]

/-- A probability measure with the expected score of the tilted counting measure has as much
entropy only if it is that measure. -/
theorem measureEntropy_eq_count_tilted_iff
    (h : ∫ s, f s ∂q = ∫ s, f s ∂(Measure.count.tilted f)) :
    Hm[q] = Hm[Measure.count.tilted f] ↔ q = Measure.count.tilted f := by
  have h1 := toReal_klDiv_count_tilted_add_measureEntropy f q
  have h2 := toReal_klDiv_count_tilted_add_measureEntropy f (Measure.count.tilted f)
  rw [klDiv_self, ENNReal.toReal_zero, zero_add] at h2
  rw [← klDiv_eq_zero_iff]
  refine ⟨fun h0 ↦ ((ENNReal.toReal_eq_zero_iff _).1 (by linarith)).resolve_right
    (klDiv_ne_top (absolutelyContinuous_count_tilted f q) .of_finite), fun h0 ↦ ?_⟩
  rw [h0, ENNReal.toReal_zero] at h1
  linarith

end InformationTheory
