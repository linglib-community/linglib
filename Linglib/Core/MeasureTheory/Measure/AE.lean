module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Filter.Ker

/-!
# The almost-everywhere filter

The kernel of the almost-everywhere filter of a measure is the set of points of positive mass,
and the almost-everywhere filter of a sum of measures is the join of theirs.

## Main statements

* `MeasureTheory.ker_ae`: `(ae μ).ker = {x | μ {x} ≠ 0}`.
* `MeasureTheory.ae_add_measure_eq`: `ae (μ + ν) = ae μ ⊔ ae ν`.
-/

@[expose] public section

open Filter Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem ker_ae (μ : Measure α) : (ae μ).ker = {x | μ {x} ≠ 0} := by
  ext x
  simp only [mem_ker, mem_ae_iff, mem_setOf_eq]
  exact ⟨fun h h0 ↦ h {x}ᶜ (by rwa [compl_compl]) rfl,
    fun h s hs ↦ by_contra fun hx ↦ h (measure_mono_null (singleton_subset_iff.2 hx) hs)⟩

theorem ae_add_measure_eq (μ ν : Measure α) : ae (μ + ν) = ae μ ⊔ ae ν := by
  ext s
  simp only [mem_ae_iff, Measure.add_apply, add_eq_zero, mem_sup]

end MeasureTheory
