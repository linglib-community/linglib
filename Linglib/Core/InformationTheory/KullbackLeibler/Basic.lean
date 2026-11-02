/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback-Leibler divergence on a finite type

On a finite type, [the divergence is the textbook relative entropy](##toReal_klDiv_eq_sum_log_div),
the expected logarithm of the ratio of the masses of the atoms.

## Implementation notes

`[UPSTREAM]` candidate for `Mathlib/InformationTheory/KullbackLeibler/Basic.lean`.

## References

* [cover-thomas-2006]
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] {μ : Measure S}

/-- On a finite type the divergence is the textbook relative entropy, the `μ`-expected log-ratio
of the masses of the atoms. -/
theorem toReal_klDiv_eq_sum_log_div [Fintype S] {ν : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ s, μ.real {s} * log (μ.real {s} / ν.real {s}) := by
  have h : llr μ ν =ᵐ[μ] fun s ↦ log (μ.real {s} / ν.real {s}) := by
    refine ae_iff_of_countable.2 fun s hs ↦ ?_
    dsimp only
    have hd := Measure.setLIntegral_rnDeriv hμν {s}
    rw [lintegral_singleton] at hd
    rw [llr, measureReal_def, measureReal_def, ← ENNReal.toReal_div, ← hd,
      ENNReal.mul_div_cancel_right (fun h ↦ hs (hμν h)) (measure_ne_top _ _)]
  rw [toReal_klDiv_of_measure_eq hμν (by simp), integral_congr_ae h, integral_fintype .of_finite]
  simp

end InformationTheory
