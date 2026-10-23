/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Factoring through a sum of functions

`Sum.elim g₁ g₂` factors through `Sum.elim f₁ f₂` exactly when each component factors
through its own and the two agree wherever `f₁` and `f₂` coincide: the factoring counterpart
of `Function.Injective.sumElim`.

`[UPSTREAM]` candidate for `Mathlib/Data/Sum/Basic.lean`, beside `Function.Injective.sumElim`.
-/

@[expose] public section

open Sum

namespace Function

variable {α β γ δ : Type*} {f₁ : α → γ} {f₂ : β → γ}
  {g₁ : α → δ} {g₂ : β → δ}

theorem FactorsThrough.sumElim (h₁ : g₁.FactorsThrough f₁)
    (h₂ : g₂.FactorsThrough f₂) (h : ∀ a b, f₁ a = f₂ b → g₁ a = g₂ b) :
    (Sum.elim g₁ g₂).FactorsThrough (Sum.elim f₁ f₂)
  | inl _, inl _, e => h₁ e
  | inl _, inr _, e => h _ _ e
  | inr _, inl _, e => (h _ _ e.symm).symm
  | inr _, inr _, e => h₂ e

theorem factorsThrough_sumElim_iff :
    (Sum.elim g₁ g₂).FactorsThrough (Sum.elim f₁ f₂) ↔
      g₁.FactorsThrough f₁ ∧ g₂.FactorsThrough f₂ ∧
        ∀ a b, f₁ a = f₂ b → g₁ a = g₂ b :=
  ⟨λ h => ⟨λ _ _ e => @h (inl _) (inl _) e, λ _ _ e => @h (inr _) (inr _) e,
    λ _ _ e => @h (inl _) (inr _) e⟩, λ ⟨h₁, h₂, h⟩ => h₁.sumElim h₂ h⟩

end Function
