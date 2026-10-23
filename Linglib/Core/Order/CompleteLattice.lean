/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# Diagonal suprema

A supremum over two indices of a family monotone in both is the supremum along the diagonal.
`[UPSTREAM]` candidate for `Mathlib/Order/CompleteLattice/Basic.lean`, beside
`iSup_iSup_eq_left`.
-/

@[expose] public section

theorem iSup_iSup_eq_iSup_diag {L : Type*} [CompleteLattice L] {g : ℕ → ℕ → L}
    (hg : ∀ m n m' n', m ≤ m' → n ≤ n' → g m n ≤ g m' n') : ⨆ m, ⨆ n, g m n = ⨆ n, g n n :=
  le_antisymm (iSup₂_le fun m n => (hg m n _ _ (le_max_left m n) (le_max_right m n)).trans
    (le_iSup (fun k => g k k) (max m n))) (iSup_le fun n => le_iSup₂ (f := g) n n)
