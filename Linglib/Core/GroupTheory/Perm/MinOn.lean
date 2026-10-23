/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Filter.Extr

/-!
# The first element of a finset under a permutation

This file counts permutations by the element of a finset that they place first. A permutation
`σ` of a finite linear order places `x` first among the elements of `D` when `x ∈ D` and `σ.symm`
attains its minimum on `D` at `x`, so that `x` comes earliest among the elements of `D` in the
sequence `σ 0, σ 1, …`. Composing `σ` with the swap of two elements of `D` exchanges which of
them comes first. A family of permutations closed under such swaps therefore places each element
of `D` first equally often, and a uniformly random permutation places each element of `D` first
with probability `1 / #D`.

## Main results

* `Equiv.Perm.card_filter_isMinOn_symm_mul_card`: in a family `S` closed under swaps of elements
  of `D`, the permutations placing an element of `Y` first among `D`, counted `#D` times, number
  `#S * #(Y ∩ D)`.
* `Equiv.Perm.card_filter_isMinOn_symm_univ_mul_card`: the same count over all permutations.
-/

@[expose] public section

open Finset

namespace Equiv.Perm

variable {α : Type*} [LinearOrder α] {D : Finset α}

theorem eq_of_isMinOn_symm {σ : Perm α} {x y : α} (hx : x ∈ D) (hy : y ∈ D)
    (hxm : IsMinOn σ.symm D x) (hym : IsMinOn σ.symm D y) : x = y :=
  σ.symm.injective ((isMinOn_iff.1 hxm y hy).antisymm (isMinOn_iff.1 hym x hx))

theorem exists_isMinOn_symm (hD : D.Nonempty) (σ : Perm α) : ∃ x ∈ D, IsMinOn σ.symm D x := by
  obtain ⟨x, hx, h⟩ := D.exists_min_image σ.symm hD
  exact ⟨x, hx, isMinOn_iff.2 h⟩

theorem isMinOn_symm_swap_mul_iff {σ : Perm α} {y y' x : α} (hy : y ∈ D) (hy' : y' ∈ D) :
    IsMinOn (swap y y' * σ).symm D (swap y y' x) ↔ IsMinOn σ.symm D x := by
  have hD (z : α) : swap y y' z ∈ D ↔ z ∈ D := by
    rcases eq_or_ne z y with rfl | h₁
    · simp [hy, hy']
    rcases eq_or_ne z y' with rfl | h₂
    · simp [hy, hy']
    rw [swap_apply_of_ne_of_ne h₁ h₂]
  have hs (z : α) : (swap y y' * σ).symm z = σ.symm (swap y y' z) := by
    rw [mul_def, symm_trans_apply, symm_swap]
  simp only [isMinOn_iff, hs, swap_apply_self]
  exact ⟨fun h z hz ↦ by simpa using h (swap y y' z) ((hD z).2 hz),
    fun h z hz ↦ h _ ((hD z).2 hz)⟩

open scoped Classical in
private theorem card_filter_isMinOn_symm_eq {S : Finset (Perm α)} {y y' : α} (hy : y ∈ D)
    (hy' : y' ∈ D) (hS : ∀ σ ∈ S, swap y y' * σ ∈ S) :
    #{σ ∈ S | IsMinOn σ.symm D y} = #{σ ∈ S | IsMinOn σ.symm D y'} := by
  refine card_bij (fun σ _ ↦ swap y y' * σ) (fun σ hσ ↦ ?_)
    (fun _ _ _ _ h ↦ mul_left_cancel h) (fun σ hσ ↦ ?_)
  · rw [mem_filter] at hσ ⊢
    refine ⟨hS σ hσ.1, ?_⟩
    simpa only [swap_apply_left] using (isMinOn_symm_swap_mul_iff (x := y) hy hy').2 hσ.2
  · rw [mem_filter] at hσ
    refine ⟨swap y y' * σ, mem_filter.2 ⟨hS σ hσ.1, ?_⟩, swap_mul_self_mul y y' σ⟩
    simpa only [swap_apply_right] using (isMinOn_symm_swap_mul_iff (x := y') hy hy').2 hσ.2

open scoped Classical in
theorem card_filter_isMinOn_symm_mul_card (S : Finset (Perm α)) (D Y : Finset α)
    (hS : ∀ y ∈ D, ∀ y' ∈ D, ∀ σ ∈ S, swap y y' * σ ∈ S) :
    #{σ ∈ S | ∃ x ∈ Y ∩ D, IsMinOn σ.symm D x} * #D = #S * #(Y ∩ D) := by
  rcases D.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp
  set F : α → Finset (Perm α) := fun y ↦ {σ ∈ S | IsMinOn σ.symm D y}
  have hcard (T : Finset α) (hT : T ⊆ D) :
      #{σ ∈ S | ∃ x ∈ T, IsMinOn σ.symm D x} = #T * #(F y₀) := by
    have hunion : {σ ∈ S | ∃ x ∈ T, IsMinOn σ.symm D x} = T.biUnion F := by
      ext σ
      simp only [F, mem_filter, mem_biUnion]
      exact ⟨fun ⟨hσ, x, hx, h⟩ ↦ ⟨x, hx, hσ, h⟩, fun ⟨x, hx, hσ, h⟩ ↦ ⟨hσ, x, hx, h⟩⟩
    have hdisj : (T : Set α).PairwiseDisjoint F := fun y hy y' hy' hne ↦
      disjoint_left.2 fun σ h h' ↦
        hne (eq_of_isMinOn_symm (hT hy) (hT hy') (mem_filter.1 h).2 (mem_filter.1 h').2)
    rw [hunion, card_biUnion hdisj]
    exact sum_const_nat fun y hy ↦
      card_filter_isMinOn_symm_eq (hT hy) hy₀ (hS y (hT hy) y₀ hy₀)
  have hall : #{σ ∈ S | ∃ x ∈ D, IsMinOn σ.symm D x} = #S :=
    congrArg card (filter_true_of_mem fun σ _ ↦ exists_isMinOn_symm ⟨y₀, hy₀⟩ σ)
  rw [hcard _ inter_subset_right, ← hall, hcard D Subset.rfl]
  ac_rfl

variable [Fintype α]

open scoped Classical in
theorem card_filter_isMinOn_symm_univ_mul_card (D Y : Finset α) :
    #{σ : Perm α | ∃ x ∈ Y ∩ D, IsMinOn σ.symm D x} * #D = (Fintype.card α).factorial *
      #(Y ∩ D) := by
  have h := card_filter_isMinOn_symm_mul_card univ D Y fun _ _ _ _ σ _ ↦ mem_univ _
  rwa [card_univ, Fintype.card_perm] at h

end Equiv.Perm
