/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Multiset.ZeroCons

/-!
# Two-element multisets

Two two-element multisets are equal exactly when their elements agree in some order, the
`Multiset` counterpart of `Sym2.eq_iff`. `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Data.Multiset.ZeroCons`, beside `Multiset.pair_comm`.
-/

public section

namespace Multiset

variable {α : Type*} {a b c d : α}

theorem pair_eq_pair_iff : ({a, b} : Multiset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  simp only [insert_eq_cons, cons_eq_cons, singleton_inj, singleton_eq_cons_iff]
  grind

end Multiset
