/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Regularity of a Stieltjes function and of its measure

A Stieltjes function is [continuous exactly where its measure has no
atom](##StieltjesFunction.continuousAt_iff_measure_singleton_eq_zero), so it is [continuous exactly
when its measure has no atoms at all](##StieltjesFunction.continuous_iff_nullSingletonClass). On a
nontrivial densely ordered domain it is [strictly monotone exactly when its measure charges every
nonempty open set](##StieltjesFunction.strictMono_iff_isOpenPosMeasure). `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/Measure/Stieltjes.lean`.
-/

public section

open MeasureTheory Set

namespace StieltjesFunction

variable {R : Type*} [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [CompactIccSpace R]
  [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]
  (f : StieltjesFunction R)

/-- A Stieltjes function is continuous at `x` iff its measure has no atom at `x`. -/
theorem continuousAt_iff_measure_singleton_eq_zero {x : R} :
    ContinuousAt f x ↔ f.measure {x} = 0 := by
  rw [measure_singleton, ENNReal.ofReal_eq_zero, sub_nonpos,
    f.mono.continuousAt_iff_leftLim_eq_rightLim, f.rightLim_eq,
    (f.mono.leftLim_le le_rfl).ge_iff_eq]

/-- A Stieltjes function is continuous iff its measure has no atoms. -/
theorem continuous_iff_nullSingletonClass : Continuous f ↔ NullSingletonClass f.measure := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_measure_singleton_eq_zero]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.measure_singleton⟩

/-- A Stieltjes function on a nontrivial densely ordered domain is strictly monotone iff its
measure charges every nonempty open set, that is, iff the support of the measure is everything. -/
theorem strictMono_iff_isOpenPosMeasure [Nontrivial R] :
    StrictMono f ↔ f.measure.IsOpenPosMeasure := by
  refine ⟨fun hf ↦ ⟨fun U hU hne ↦ ?_⟩, fun _ a b hab ↦ ?_⟩
  · obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hne
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    refine (lt_of_lt_of_le ?_ (measure_mono hsub)).ne'
    rw [measure_Ioo, ENNReal.ofReal_pos, sub_pos]
    exact (hf hac).trans_le (f.mono.le_leftLim hcb)
  · have h := (isOpen_Ioo.measure_pos f.measure (nonempty_Ioo.2 hab)).trans_le
      (measure_mono Ioo_subset_Ioc_self)
    rwa [measure_Ioc, ENNReal.ofReal_pos, sub_pos] at h

end StieltjesFunction
