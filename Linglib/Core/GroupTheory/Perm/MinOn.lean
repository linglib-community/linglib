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
sequence `σ 0, σ 1, …`. Composing `σ` with a permutation `g` that preserves `D` moves the first
element along `g`. A family of permutations therefore places each element of `D` first equally
often when the permutations preserving it and `D` act transitively on `D`, and a uniformly random
permutation places each element of `D` first with probability `1 / #D`.

## Main results

* `Equiv.Perm.card_filter_isMinOn_symm_mul_card`: in a family `S` whose symmetries act
  transitively on `D`, the permutations placing an element of `Y` first among `D`, counted `#D`
  times, number `#S * #(Y ∩ D)`.
* `Equiv.Perm.card_filter_isMinOn_symm_univ_mul_card`: the same count over all permutations.
-/

public section

open Finset

namespace Equiv.Perm

variable {α : Type*} [LinearOrder α] {D : Finset α}

theorem eq_of_isMinOn_symm {σ : Perm α} {x y : α} (hx : x ∈ D) (hy : y ∈ D)
    (hxm : IsMinOn σ.symm D x) (hym : IsMinOn σ.symm D y) : x = y :=
  σ.symm.injective ((isMinOn_iff.1 hxm y hy).antisymm (isMinOn_iff.1 hym x hx))

theorem exists_isMinOn_symm (hD : D.Nonempty) (σ : Perm α) : ∃ x ∈ D, IsMinOn σ.symm D x := by
  obtain ⟨x, hx, h⟩ := D.exists_min_image σ.symm hD
  exact ⟨x, hx, isMinOn_iff.2 h⟩

theorem swap_apply_mem_iff {y y' : α} (hy : y ∈ D) (hy' : y' ∈ D) (z : α) :
    swap y y' z ∈ D ↔ z ∈ D := by
  rcases eq_or_ne z y with rfl | h₁
  · simp [hy, hy']
  rcases eq_or_ne z y' with rfl | h₂
  · simp [hy, hy']
  rw [swap_apply_of_ne_of_ne h₁ h₂]

/-- A permutation `g` that preserves `D` carries the element that `σ` places first among `D` to
the one that `g * σ` places first. -/
theorem isMinOn_symm_mul_iff {σ g : Perm α} {x : α} (hg : ∀ z, g z ∈ D ↔ z ∈ D) :
    IsMinOn (g * σ).symm D (g x) ↔ IsMinOn σ.symm D x := by
  have hs (z : α) : (g * σ).symm z = σ.symm (g.symm z) := rfl
  simp only [isMinOn_iff, hs, symm_apply_apply]
  exact ⟨fun h z hz ↦ by simpa using h (g z) ((hg z).2 hz),
    fun h z hz ↦ h _ ((hg _).1 (by simpa using hz))⟩

open scoped Classical in
private theorem card_filter_isMinOn_symm_eq {S : Finset (Perm α)} {g : Perm α} (y : α)
    (hg : ∀ z, g z ∈ D ↔ z ∈ D) (hS : ∀ σ, g * σ ∈ S ↔ σ ∈ S) :
    #{σ ∈ S | IsMinOn σ.symm D y} = #{σ ∈ S | IsMinOn σ.symm D (g y)} := by
  refine card_bij (fun σ _ ↦ g * σ) (fun σ hσ ↦ ?_)
    (fun _ _ _ _ h ↦ mul_left_cancel h) (fun σ hσ ↦ ?_)
  · rw [mem_filter] at hσ ⊢
    exact ⟨(hS σ).2 hσ.1, (isMinOn_symm_mul_iff hg).2 hσ.2⟩
  · rw [mem_filter] at hσ
    refine ⟨g⁻¹ * σ, mem_filter.2 ⟨(hS _).1 (by rw [mul_inv_cancel_left]; exact hσ.1), ?_⟩,
      mul_inv_cancel_left g σ⟩
    exact (isMinOn_symm_mul_iff hg).1 (by rw [mul_inv_cancel_left]; exact hσ.2)

open scoped Classical in
/-- In a family `S` of permutations on which the permutations preserving both `S` and `D` act
transitively on `D`, the permutations placing an element of `Y` first among `D`, counted `#D`
times, number `#S * #(Y ∩ D)`. -/
theorem card_filter_isMinOn_symm_mul_card (S : Finset (Perm α)) (D Y : Finset α)
    (hS : ∀ y ∈ D, ∀ y' ∈ D, ∃ g : Perm α,
      g y = y' ∧ (∀ z, g z ∈ D ↔ z ∈ D) ∧ ∀ σ, g * σ ∈ S ↔ σ ∈ S) :
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
    refine sum_const_nat fun y hy ↦ ?_
    obtain ⟨g, hgy, hg, hgS⟩ := hS y (hT hy) y₀ hy₀
    exact hgy ▸ card_filter_isMinOn_symm_eq y hg hgS
  have hall : #{σ ∈ S | ∃ x ∈ D, IsMinOn σ.symm D x} = #S :=
    congrArg card (filter_true_of_mem fun σ _ ↦ exists_isMinOn_symm ⟨y₀, hy₀⟩ σ)
  rw [hcard _ inter_subset_right, ← hall, hcard D Subset.rfl]
  ac_rfl

variable [Fintype α]

open scoped Classical in
/-- The permutations placing an element of `Y` first among `D`, counted `#D` times, number
`(card α)! * #(Y ∩ D)`. -/
theorem card_filter_isMinOn_symm_univ_mul_card (D Y : Finset α) :
    #{σ : Perm α | ∃ x ∈ Y ∩ D, IsMinOn σ.symm D x} * #D = (Fintype.card α).factorial *
      #(Y ∩ D) := by
  have h := card_filter_isMinOn_symm_mul_card univ D Y fun y hy y' hy' ↦
    ⟨swap y y', swap_apply_left y y', swap_apply_mem_iff hy hy', fun _ ↦ by simp⟩
  rwa [card_univ, Fintype.card_perm] at h

end Equiv.Perm
