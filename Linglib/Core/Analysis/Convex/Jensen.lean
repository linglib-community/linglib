/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Function

/-!
# Jensen's inequality over a semifield

In this file we prove the finite Jensen inequality for a module over a linearly ordered semifield.
See `Convex.sum_smul_mem` and `ConvexOn.map_sum_smul_le`.

Mathlib proves it for a module over a field, in `Mathlib.Analysis.Convex.Jensen`. A convex
combination involves no subtraction, so a semifield is enough. The extra generality matters for
measures: they form a module over `ℝ≥0`, and a convex combination of measures is a mixture.

[UPSTREAM] generalizations of `Convex.sum_mem` and `ConvexOn.map_sum_le`.
-/

@[expose] public section

variable {𝕜 E β ι : Type*} [Semifield 𝕜]

private theorem sum_smul_eq_smul_sum_div {M : Type*} [AddCommMonoid M] [Module 𝕜 M]
    (t : Finset ι) (w : ι → 𝕜) (z : ι → M) {c : 𝕜} (hc : c ≠ 0) :
    ∑ j ∈ t, w j • z j = c • ∑ j ∈ t, (w j / c) • z j := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_smul, mul_div_cancel₀ _ hc]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E] {s : Set E}
  {t : Finset ι} {w : ι → 𝕜} {p : ι → E}

/-- A convex set contains the convex combinations of its points. -/
theorem Convex.sum_smul_mem (hs : Convex 𝕜 s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hp : ∀ i ∈ t, p i ∈ s) : ∑ i ∈ t, w i • p i ∈ s := by
  classical
  induction t using Finset.induction_on generalizing w with
  | empty => simp at h₁
  | insert i t hi ih =>
    rw [Finset.sum_insert hi] at h₁ ⊢
    have hpi := hp i (Finset.mem_insert_self i t)
    have h₀t : ∀ j ∈ t, 0 ≤ w j := fun j hj ↦ h₀ j (Finset.mem_insert_of_mem hj)
    rcases eq_or_ne (∑ j ∈ t, w j) 0 with hc | hc
    · rw [hc, add_zero] at h₁
      rw [Finset.sum_eq_zero fun j hj ↦ by
        rw [(Finset.sum_eq_zero_iff_of_nonneg h₀t).1 hc j hj, zero_smul], h₁]
      simpa using hpi
    · have hcpos : 0 < ∑ j ∈ t, w j := (Finset.sum_nonneg h₀t).lt_of_ne' hc
      have hq := ih (w := fun j ↦ w j / ∑ j ∈ t, w j)
        (fun j hj ↦ div_nonneg (h₀t j hj) hcpos.le) (by rw [← Finset.sum_div, div_self hc])
        fun j hj ↦ hp j (Finset.mem_insert_of_mem hj)
      rw [sum_smul_eq_smul_sum_div t w p hc]
      exact hs hpi hq (h₀ i (Finset.mem_insert_self i t)) hcpos.le h₁

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β]
  [PosSMulMono 𝕜 β] {f : E → β}

/-- Jensen's inequality for finite sums: the value of a convex function at a convex combination
is at most the combination of its values. -/
theorem ConvexOn.map_sum_smul_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hp : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) := by
  classical
  induction t using Finset.induction_on generalizing w with
  | empty => simp at h₁
  | insert i t hi ih =>
    rw [Finset.sum_insert hi] at h₁ ⊢
    rw [Finset.sum_insert hi]
    have hpi := hp i (Finset.mem_insert_self i t)
    have h₀t : ∀ j ∈ t, 0 ≤ w j := fun j hj ↦ h₀ j (Finset.mem_insert_of_mem hj)
    rcases eq_or_ne (∑ j ∈ t, w j) 0 with hc | hc
    · have h0 := (Finset.sum_eq_zero_iff_of_nonneg h₀t).1 hc
      rw [hc, add_zero] at h₁
      rw [Finset.sum_eq_zero fun j hj ↦ by rw [h0 j hj, zero_smul],
        Finset.sum_eq_zero fun j hj ↦ by rw [h0 j hj, zero_smul], h₁]
      simp
    · have hcpos : 0 < ∑ j ∈ t, w j := (Finset.sum_nonneg h₀t).lt_of_ne' hc
      have hw' : ∑ j ∈ t, w j / ∑ j ∈ t, w j = 1 := by rw [← Finset.sum_div, div_self hc]
      have h₀' : ∀ j ∈ t, 0 ≤ w j / ∑ j ∈ t, w j := fun j hj ↦ div_nonneg (h₀t j hj) hcpos.le
      have hpt : ∀ j ∈ t, p j ∈ s := fun j hj ↦ hp j (Finset.mem_insert_of_mem hj)
      rw [sum_smul_eq_smul_sum_div t w p hc, sum_smul_eq_smul_sum_div t w (fun j ↦ f (p j)) hc]
      exact (hf.2 hpi (hf.1.sum_smul_mem h₀' hw' hpt) (h₀ i (Finset.mem_insert_self i t))
        hcpos.le h₁).trans (add_le_add le_rfl (smul_le_smul_of_nonneg_left (ih h₀' hw' hpt)
          hcpos.le))
