/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Function.EssSup

/-!
# The essential infimum on a countable space

On a countable space a property holds almost everywhere exactly when it holds at every atom of
positive mass, so the essential infimum of a function is its infimum over those atoms. This
generalizes `essInf_eq_iInf`, where every atom has positive mass.

## Main results

* `MeasureTheory.essInf_eq_biInf`: on a countable space the essential infimum is the infimum
  over the atoms of positive mass.
* `MeasureTheory.essInf_eq_zero_iff`: on a finite space the essential infimum of a function into
  `ℝ≥0∞` vanishes exactly when the function vanishes at an atom of positive mass.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [Countable α]

theorem essInf_eq_biInf [CompleteLattice β] (f : α → β) :
    essInf f μ = ⨅ a ∈ {a | μ {a} ≠ 0}, f a := by
  rw [essInf, Filter.liminf_eq, ← sInf_image, ← sSup_lowerBounds_eq_sInf]
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq, mem_lowerBounds, Set.forall_mem_image]
  exact ae_iff_of_countable

theorem essInf_eq_zero_iff [Finite α] {f : α → ℝ≥0∞} :
    essInf f μ = 0 ↔ ∃ a, μ {a} ≠ 0 ∧ f a = 0 := by
  classical
  have := Fintype.ofFinite α
  rw [essInf_eq_biInf]
  refine ⟨fun h ↦ ?_, fun ⟨a, ha, hf⟩ ↦ le_antisymm ((iInf₂_le a ha).trans hf.le) zero_le⟩
  set s := Finset.univ.filter fun a ↦ μ {a} ≠ 0
  have hs : ⨅ a ∈ {a | μ {a} ≠ 0}, f a = s.inf f := by simp [s, Finset.inf_eq_iInf]
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [hs, he, Finset.inf_empty] at h
    exact absurd h ENNReal.top_ne_zero
  · obtain ⟨a, ha, hfa⟩ := Finset.exists_mem_eq_inf s hne f
    exact ⟨a, (Finset.mem_filter.1 ha).2, hfa ▸ hs ▸ h⟩

end MeasureTheory
