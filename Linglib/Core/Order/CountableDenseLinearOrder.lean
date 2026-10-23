/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.CountableDenseLinearOrder

/-!
# Countable strict weak orders embed in the rationals

`[UPSTREAM]` candidate for `Mathlib/Order/CountableDenseLinearOrder.lean`. A countable strict
weak order is the pullback of `<` on `ℚ` along some map. Its quotient by incomparability is a
countable linear order, which embeds in `ℚ` by Cantor's theorem
`Order.embedding_from_countable_to_dense`.
-/

@[expose] public section

namespace Order

theorem exists_rat_rel_iff_lt {β : Type*} [Countable β] (r : β → β → Prop)
    [IsStrictWeakOrder β r] : ∃ f : β → ℚ, ∀ x y, r x y ↔ f x < f y := by
  classical
  have neg_trans {a b c : β} (h₁ : ¬ r a b) (h₂ : ¬ r b c) : ¬ r a c := fun h ↦ by
    by_cases hba : r b a
    · exact h₂ (_root_.trans hba h)
    by_cases hcb : r c b
    · exact h₁ (_root_.trans h hcb)
    exact (IsStrictWeakOrder.incomp_trans a b c ⟨h₁, hba⟩ ⟨h₂, hcb⟩).1 h
  let : Preorder β :=
    { le x y := ¬ r y x
      lt := r
      le_refl x := irrefl x
      le_trans _ _ _ h₁ h₂ := neg_trans h₂ h₁
      lt_iff_le_not_ge _ _ := ⟨fun h ↦ ⟨asymm h, not_not.2 h⟩, fun h ↦ not_not.1 h.2⟩ }
  have : Std.Total (α := β) (· ≤ ·) := ⟨fun x y ↦ (em (r y x)).elim (.inr <| asymm ·) .inl⟩
  have : Countable (Antisymmetrization β (· ≤ ·)) := Quotient.countable
  obtain ⟨e⟩ := embedding_from_countable_to_dense (Antisymmetrization β (· ≤ ·)) ℚ
  exact ⟨fun x ↦ e (toAntisymmetrization _ x), fun _ _ ↦ by rw [e.lt_iff_lt]; rfl⟩

end Order
