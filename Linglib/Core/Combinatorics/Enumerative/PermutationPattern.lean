/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Order patterns of a random permutation

Fix an injective tuple `q : Fin k ↪ α` in a finite linear order. A permutation `σ` of `α`
realizes on `q` the order pattern `Tuple.sort (σ ∘ q)`, the reordering of `Fin k` that sorts
`σ ∘ q`. Each of the `k !` patterns is realized by the same number of permutations, so a
uniformly random permutation realizes each one with probability `1 / k !`.

## Main statements

* `Equiv.Perm.factorial_mul_card_sort_comp_eq`: `k ! * #{σ | sort (σ ∘ q) = ρ} = (card α)!`.
* `Equiv.Perm.factorial_mul_card_monotone_comp`: `k ! * #{σ | Monotone (σ ∘ q)} = (card α)!`.

## Implementation notes

Sorting a reordered injective tuple undoes the reordering, and `ρ.viaEmbedding q` turns
precomposition of `q` by `ρ` into postcomposition, so right multiplication by it carries the
permutations realizing `ρ` onto those realizing the identity pattern.

[UPSTREAM] `Tuple.sort_comp_perm_of_injective` belongs in `Mathlib/Data/Fin/Tuple/Sort.lean`, the
counts in `Mathlib/Combinatorics/Enumerative/PermutationPattern.lean`.
-/

@[expose] public section

open Finset Nat

namespace Tuple

variable {n : ℕ} {α : Type*} [LinearOrder α] {f : Fin n → α}

theorem sort_comp_perm_of_injective (hf : Function.Injective f) (σ : Equiv.Perm (Fin n)) :
    sort (f ∘ σ) = σ⁻¹ * sort f := by
  refine Equiv.ext fun i ↦ ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]
  exact hf (congrFun comp_perm_comp_sort_eq_comp_sort i)

end Tuple

namespace Equiv.Perm

variable {α : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] {k : ℕ}

private theorem card_sort_comp_eq (q : Fin k ↪ α) (ρ : Perm (Fin k)) :
    #{σ : Perm α | Tuple.sort (σ ∘ q) = ρ} = #{σ : Perm α | Tuple.sort (σ ∘ q) = 1} := by
  refine card_equiv (Equiv.mulRight (ρ.viaEmbedding q)) fun σ ↦ ?_
  have : (σ ∘ ρ.viaEmbedding q) ∘ q = (σ ∘ q) ∘ ρ :=
    funext fun i ↦ congrArg σ (viaEmbedding_apply ρ q i)
  simp only [mem_filter, mem_univ, true_and, coe_mulRight, coe_mul, this,
    Tuple.sort_comp_perm_of_injective (σ.injective.comp q.injective), inv_mul_eq_one]
  exact eq_comm

/-- **Order patterns are uniform**: each reordering of `Fin k` is the order pattern of one
permutation in `k !` on a fixed injective tuple. -/
theorem factorial_mul_card_sort_comp_eq (q : Fin k ↪ α) (ρ : Perm (Fin k)) :
    k ! * #{σ : Perm α | Tuple.sort (σ ∘ q) = ρ} = (Fintype.card α)! := by
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Perm α))) (t := univ)
    (f := fun σ : Perm α ↦ Tuple.sort (σ ∘ q)) fun _ _ ↦ mem_coe.2 (mem_univ _)
  rw [sum_const_nat fun τ _ ↦ (card_sort_comp_eq q τ).trans (card_sort_comp_eq q ρ).symm,
    card_univ, card_univ, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin] at h
  exact h.symm

/-- One permutation in `k !` leaves a fixed injective tuple in increasing order. -/
theorem factorial_mul_card_monotone_comp (q : Fin k ↪ α) :
    k ! * #{σ : Perm α | Monotone (σ ∘ q)} = (Fintype.card α)! := by
  simpa only [one_def, Tuple.sort_eq_refl_iff_monotone] using factorial_mul_card_sort_comp_eq q 1

end Equiv.Perm
