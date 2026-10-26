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

* `essInf_eq_biInf`: on a countable space the essential infimum is the infimum over the atoms of
  positive mass.
* `essInf_eq_bot_iff`: on a finite space the essential infimum is `⊥` exactly when the function
  is `⊥` at an atom of positive mass.
-/

@[expose] public section

open MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α}

theorem essInf_eq_biInf [Countable α] [CompleteLattice β] (f : α → β) :
    essInf f μ = ⨅ (a) (_ : μ {a} ≠ 0), f a := by
  rw [essInf, Filter.liminf_eq]
  simp_rw [ae_iff_of_countable, ← le_iInf₂_iff]
  exact csSup_Iic

theorem essInf_eq_bot_iff [Finite α] [CompleteLinearOrder β] [Nontrivial β] {f : α → β} :
    essInf f μ = ⊥ ↔ ∃ a, μ {a} ≠ 0 ∧ f a = ⊥ := by
  classical
  have := Fintype.ofFinite α
  have hs : ⨅ (a) (_ : μ {a} ≠ 0), f a = (Finset.univ.filter fun a ↦ μ {a} ≠ 0).inf f := by
    simp [Finset.inf_eq_iInf]
  rw [essInf_eq_biInf, hs, Finset.inf_eq_bot_iff]
  simp

theorem ENNReal.essInf_eq_zero_iff [Finite α] {f : α → ENNReal} :
    essInf f μ = 0 ↔ ∃ a, μ {a} ≠ 0 ∧ f a = 0 :=
  essInf_eq_bot_iff
