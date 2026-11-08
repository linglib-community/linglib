/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.UniformOn

/-!
# The uniform measure on a finite set

`ProbabilityTheory.uniformOn s` gives `t` the proportion $|s ∩ t| / |s|$, and is `0` when `s` is
infinite. This file evaluates it in `ℝ≥0∞` and on reals, at points, finsets and predicates, and
computes its almost-everywhere filter, the principal filter of `s`. On `Set.univ` of a finite type
that filter is `⊤`, so the uniform measure there dominates every measure.

## TODO

Choose a simp normal form for the evaluations at points, as mathlib's `uniformOfFinset` does.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {s t : Set Ω} {ω : Ω}

/-! ### Proportions -/

/-- The uniform measure on `s` gives `t` the proportion of `s` lying in `t`. An infinite `s` makes
both sides `0`. -/
theorem uniformOn_apply (s t : Set Ω) : uniformOn s t = (s ∩ t).encard / s.encard := by
  rcases s.finite_or_infinite with hs | hs
  · rw [uniformOn, cond_apply hs.measurableSet, Measure.count_apply hs.measurableSet,
      Measure.count_apply (hs.inter_of_left t).measurableSet, ENNReal.div_eq_inv_mul]
  · simp [uniformOn_eq_zero.2 (.inl hs), hs.encard_eq]

theorem uniformOn_apply_of_finite (hs : s.Finite) (t : Set Ω) :
    uniformOn s t = (s ∩ t).ncard / s.ncard := by
  rw [uniformOn_apply, ← hs.cast_ncard_eq, ← (hs.inter_of_left t).cast_ncard_eq]
  simp only [ENat.toENNReal_coe]

theorem uniformOn_real_apply_of_finite (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = (s ∩ t).ncard / s.ncard := by
  rw [measureReal_def, uniformOn_apply_of_finite hs, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

theorem uniformOn_real_apply [Finite Ω] (s t : Set Ω) :
    (uniformOn s).real t = (s ∩ t).ncard / s.ncard :=
  uniformOn_real_apply_of_finite s.toFinite t

theorem uniformOn_ne_zero_iff (hs : s.Finite) : uniformOn s t ≠ 0 ↔ (s ∩ t).Nonempty :=
  (uniformOn_eq_zero_iff hs).not.trans nonempty_iff_ne_empty.symm

theorem uniformOn_eq_one_iff (hs : s.Finite) (hne : s.Nonempty) : uniformOn s t = 1 ↔ s ⊆ t :=
  ⟨pred_true_of_uniformOn_eq_one, uniformOn_eq_one_of hs hne⟩

theorem uniformOn_apply_singleton_of_mem (hs : s.Finite) (hω : ω ∈ s) :
    uniformOn s {ω} = (s.ncard : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_apply_of_finite hs, inter_singleton_of_mem hω, ncard_singleton, Nat.cast_one,
    one_div]

theorem uniformOn_apply_singleton_of_notMem (hω : ω ∉ s) : uniformOn s {ω} = 0 := by
  rw [uniformOn, cond_apply' (measurableSet_singleton ω), inter_singleton_of_notMem hω,
    measure_empty, mul_zero]

theorem uniformOn_cond (hs : s.Finite) (ht : MeasurableSet t) :
    (uniformOn s)[|t] = uniformOn (s ∩ t) := by
  rw [uniformOn, uniformOn,
    cond_cond_eq_cond_inter' hs.measurableSet ht (Measure.count_apply_lt_top.2 hs).ne]

theorem uniformOn_univ_cond [Finite Ω] (t : Set Ω) :
    (uniformOn (univ : Set Ω))[|t] = uniformOn t := by
  rw [uniformOn_cond finite_univ t.toFinite.measurableSet, univ_inter]

/-! ### Null sets -/

/-- A set is conull for the uniform measure on a finite set `s` exactly when it contains `s`. -/
theorem ae_uniformOn (hs : s.Finite) : ae (uniformOn s) = 𝓟 s := by
  ext t
  rw [mem_ae_iff, mem_principal, uniformOn_eq_zero_iff hs, ← sdiff_eq, sdiff_eq_empty]

theorem uniformOn_absolutelyContinuous_of_subset (ht : t.Finite) (hst : s ⊆ t) :
    uniformOn s ≪ uniformOn t := by
  rw [← Measure.ae_le_iff_absolutelyContinuous, ae_uniformOn ht, ae_uniformOn (ht.subset hst)]
  exact principal_mono.2 hst

/-! ### Finsets -/

theorem uniformOn_finset_apply_singleton [DecidableEq Ω] (s : Finset Ω) (ω : Ω) :
    uniformOn ↑s {ω} = if ω ∈ s then (#s : ℝ≥0∞)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  split_ifs with h <;> simp [Finset.inter_singleton_of_mem, Finset.inter_singleton_of_notMem, h,
    div_eq_mul_inv]

theorem uniformOn_finset_real_singleton [DecidableEq Ω] (s : Finset Ω) (ω : Ω) :
    (uniformOn (s : Set Ω)).real {ω} = if ω ∈ s then (#s : ℝ)⁻¹ else 0 := by
  rw [measureReal_def, uniformOn_finset_apply_singleton]
  split_ifs <;> simp

theorem uniformOn_finset_setOf (s : Finset Ω) (p : Ω → Prop) [DecidablePred p] :
    uniformOn (s : Set Ω) {ω | p ω} = #(s.filter p) / #s := by
  classical
  rw [← uniformOn_inter_self s.finite_toSet, show (s : Set Ω) ∩ {ω | p ω} = ↑(s.filter p) by
    ext; simp, uniformOn_apply_finset, Finset.inter_eq_right.2 (Finset.filter_subset _ _)]

theorem uniformOn_finset_real_setOf (s : Finset Ω) (p : Ω → Prop) [DecidablePred p] :
    (uniformOn (s : Set Ω)).real {ω | p ω} = #(s.filter p) / #s := by
  rw [measureReal_def, uniformOn_finset_setOf, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

/-! ### The uniform measure on a finite type -/

section Finite

variable [Finite Ω]

theorem uniformOn_univ_singleton_ne_zero (ω : Ω) : uniformOn (univ : Set Ω) {ω} ≠ 0 :=
  (uniformOn_ne_zero_iff finite_univ).2 ⟨ω, trivial, rfl⟩

@[simp]
theorem ae_uniformOn_univ : ae (uniformOn (univ : Set Ω)) = ⊤ := by
  rw [ae_uniformOn finite_univ, principal_univ]

theorem absolutelyContinuous_uniformOn_univ (μ : Measure Ω) : μ ≪ uniformOn univ :=
  (le_top.trans_eq ae_uniformOn_univ.symm).absolutelyContinuous_of_ae

end Finite

section Fintype

variable [Fintype Ω]

theorem uniformOn_univ_apply_singleton (ω : Ω) :
    uniformOn (univ : Set Ω) {ω} = (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, one_div]

theorem uniformOn_univ_real_singleton (ω : Ω) :
    (uniformOn (univ : Set Ω)).real {ω} = (Fintype.card Ω : ℝ)⁻¹ := by
  rw [measureReal_def, uniformOn_univ_apply_singleton, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem uniformOn_univ_singleton_eq (ω ω' : Ω) :
    uniformOn (univ : Set Ω) {ω} = uniformOn univ {ω'} := by
  rw [uniformOn_univ_apply_singleton, uniformOn_univ_apply_singleton]

theorem uniformOn_univ_real_apply (s : Set Ω) :
    (uniformOn (univ : Set Ω)).real s = s.ncard / Fintype.card Ω := by
  rw [uniformOn_real_apply, univ_inter, ncard_univ, Nat.card_eq_fintype_card]

theorem uniformOn_univ_le_iff [Nonempty Ω] :
    uniformOn (univ : Set Ω) s ≤ uniformOn univ t ↔ s.ncard ≤ t.ncard := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, uniformOn_univ_real_apply, uniformOn_univ_real_apply,
    div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos), Nat.cast_le]

end Fintype

end ProbabilityTheory
