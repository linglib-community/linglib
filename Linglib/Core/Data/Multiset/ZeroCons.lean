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

@[expose] public section

namespace Multiset

variable {α : Type*} {a b c d : α}

/-- Two two-element multisets are equal exactly when their elements agree in some order. -/
theorem pair_eq_pair_iff : ({a, b} : Multiset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [insert_eq_cons] at h
    rcases mem_cons.1 (h ▸ mem_cons_self a {b}) with rfl | ha
    · exact .inl ⟨rfl, singleton_inj.1 ((cons_inj_right a).1 h)⟩
    · obtain rfl := mem_singleton.1 ha
      exact .inr ⟨rfl, singleton_inj.1 ((cons_inj_right a).1 (h.trans (pair_comm c a)))⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [rfl, pair_comm _ _]

end Multiset
