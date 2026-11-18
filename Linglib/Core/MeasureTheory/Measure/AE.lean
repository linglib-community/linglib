module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Filter.Ker

/-!
# The almost-everywhere filter

The [kernel](##MeasureTheory.ker_ae) of the almost-everywhere filter of a measure is the set of
points of positive mass, and the almost-everywhere filter of a
[sum of two measures](##MeasureTheory.ae_add_measure_eq) is the join of theirs, the binary case
of mathlib's `MeasureTheory.Measure.ae_sum_eq`. `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/Measure/Restrict.lean`, beside `ae_add_measure_iff`.
-/

public section

open Filter Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem ker_ae (μ : Measure α) : (ae μ).ker = {x | μ {x} ≠ 0} := by
  ext x
  simp only [mem_ker, mem_ae_iff, mem_ofPred_eq]
  exact ⟨fun h h0 ↦ h {x}ᶜ (by rwa [compl_compl]) rfl,
    fun h s hs ↦ by_contra fun hx ↦ h (measure_mono_null (singleton_subset_iff.2 hx) hs)⟩

theorem ae_add_measure_eq (μ ν : Measure α) : ae (μ + ν) = ae μ ⊔ ae ν :=
  Filter.ext fun _ ↦ ae_add_measure_iff

end MeasureTheory
