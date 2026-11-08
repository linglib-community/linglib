/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Independent events

Lemmas on mathlib's `IndepSet` that mathlib does not state: symmetry and complements, the
independence of null and sure events from every event, the product rule and the
inclusion-exclusion law on real-valued masses, the conditional probability of one independent
event given the other, and independence under a uniform measure as an equation between counts.
`[UPSTREAM]` candidates for `Mathlib/Probability/Independence/Basic.lean`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t : Set Ω}

@[symm]
theorem IndepSet.symm (h : IndepSet s t μ) : IndepSet t s μ :=
  Indep.symm h

theorem IndepSet.compl_left (h : IndepSet s t μ) : IndepSet sᶜ t μ :=
  Indep.indepSet_of_measurableSet h
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton s)).compl
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton t))

theorem IndepSet.measureReal_inter_eq_mul (h : IndepSet s t μ) :
    μ.real (s ∩ t) = μ.real s * μ.real t := by
  simp only [measureReal_def, h.measure_inter_eq_mul, ENNReal.toReal_mul]

theorem indepSet_iff_measureReal_inter_eq_mul [IsZeroOrProbabilityMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) : IndepSet s t μ ↔ μ.real (s ∩ t) = μ.real s * μ.real t := by
  rw [indepSet_iff_measure_inter_eq_mul hs ht μ, measureReal_def, measureReal_def,
    measureReal_def, ← ENNReal.toReal_mul, ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (by finiteness)]

theorem indepSet_of_measure_eq_zero_right [IsZeroOrProbabilityMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : μ t = 0) : IndepSet s t μ :=
  (indepSet_iff_measure_inter_eq_mul hs ht μ).2 <| by
    rw [measure_mono_null Set.inter_subset_right h, h, mul_zero]

theorem indepSet_of_measure_compl_eq_zero_right [IsZeroOrProbabilityMeasure μ]
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h : μ tᶜ = 0) : IndepSet s t μ := by
  simpa using (indepSet_of_measure_eq_zero_right hs ht.compl h).symm.compl_left.symm

theorem IndepSet.measureReal_union (h : IndepSet s t μ) (ht : MeasurableSet t)
    (hs' : μ s ≠ ∞ := by finiteness) (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t - μ.real s * μ.real t := by
  rw [eq_sub_iff_add_eq, ← h.measureReal_inter_eq_mul, measureReal_union_add_inter ht hs' ht']

/-- Conditioning on one of two independent events leaves the probability of the other unchanged. -/
theorem IndepSet.cond_apply (h : IndepSet s t μ) (hs : MeasurableSet s) (hs₀ : μ s ≠ 0)
    (hs' : μ s ≠ ∞ := by finiteness) : μ[t|s] = μ t := by
  rw [ProbabilityTheory.cond_apply hs, h.measure_inter_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel hs₀ hs', one_mul]

theorem IndepSet.cond_real_apply (h : IndepSet s t μ) (hs : MeasurableSet s) (hs₀ : μ s ≠ 0)
    (hs' : μ s ≠ ∞ := by finiteness) : μ[|s].real t = μ.real t :=
  congrArg ENNReal.toReal (h.cond_apply hs hs₀ hs')

/-- Under the uniform measure on a finite set `u`, two events are independent when the count of
their intersection within `u`, scaled by the size of `u`, is the product of their counts. -/
theorem indepSet_uniformOn_iff [Finite Ω] [MeasurableSingletonClass Ω] (u : Set Ω) :
    IndepSet s t (uniformOn u) ↔ (u ∩ (s ∩ t)).ncard * u.ncard = (u ∩ s).ncard * (u ∩ t).ncard := by
  rw [indepSet_iff_measureReal_inter_eq_mul (Set.toFinite s).measurableSet
    (Set.toFinite t).measurableSet, uniformOn_real_apply, uniformOn_real_apply,
    uniformOn_real_apply]
  rcases Nat.eq_zero_or_pos u.ncard with h0 | h0
  · have hz : ∀ v, (u ∩ v).ncard = 0 := fun v ↦
      Nat.eq_zero_of_le_zero (h0 ▸ Set.ncard_le_ncard Set.inter_subset_left u.toFinite)
    simp [h0, hz]
  · rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    norm_cast
    rw [← mul_assoc, Nat.mul_left_inj h0.ne']

end ProbabilityTheory
