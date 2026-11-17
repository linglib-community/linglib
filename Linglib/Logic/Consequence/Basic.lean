/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Concept

/-!
# Consequence

The semantics of a logic is a relation of satisfaction between models and formulas. A formula
$\varphi$ is a [consequence](##Entails) of a set $\Gamma$ of formulas when every model satisfying
$\Gamma$ satisfies $\varphi$. Taking consequences is [a closure
operator](##entails_iff_mem_intentClosure) on sets of formulas: a set [entails its
members](##Entails.of_mem), consequences [survive added premises](##Entails.weaken), and what
follows from consequences of $\Gamma$ [follows from $\Gamma$](##Entails.trans). Consequence
[transfers along a map of models](##Entails.comap) that preserves and reflects satisfaction, so
it [survives restriction](##Entails.restrict) to a class of admissible models.

## Implementation notes

* A notion of satisfaction is a relation `Model → Formula → Prop`. A logic states its consequence
  relation as `Γ ⊨[p] φ` for its own satisfaction relation `p`, with everything its definition
  quantifies over bundled into the model type.
* The models of a set of formulas and the theory of a class of models are the polars
  `lowerPolar p Γ` and `upperPolar p K` of `Mathlib.Order.Concept`, without names of their own.
* Premises are sets, as theories are in `Mathlib.ModelTheory`, so the order and multiplicity of
  premises play no role and consequence is monotone in them. The order-sensitive consequence
  relations of update semantics take lists of updates and are in
  `Semantics/Dynamic/Consequence.lean`.

## References

* [tarski-1956]
-/

@[expose] public section

namespace Consequence

variable {Model Formula : Type*} {p : Model → Formula → Prop} {Γ Γ' Θ : Set Formula}
  {φ : Formula}

/-- `Γ ⊨[p] φ`: the formula `φ` is a consequence of `Γ` when every model satisfying all of `Γ`
satisfies `φ`. -/
def Entails (p : Model → Formula → Prop) (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ M, (∀ γ ∈ Γ, p M γ) → p M φ

@[inherit_doc] scoped notation:50 Γ " ⊨[" p "] " φ:51 => Entails p Γ φ

/-- The consequences of `Γ` are its closure under the closure operator of the satisfaction
relation, so consequence is extensive, monotone and idempotent ([tarski-1956], Axioms 2 and 3 of
*On some fundamental concepts of metamathematics*). -/
theorem entails_iff_mem_intentClosure : Γ ⊨[p] φ ↔ φ ∈ intentClosure p Γ :=
  .rfl

namespace Entails

theorem of_mem (h : φ ∈ Γ) : Γ ⊨[p] φ := fun _ hΓ ↦ hΓ φ h

theorem weaken (hΓ : Γ ⊆ Γ') (h : Γ ⊨[p] φ) : Γ' ⊨[p] φ := fun M hM ↦
  h M fun γ hγ ↦ hM γ (hΓ hγ)

/-- Whatever follows from consequences of `Γ` follows from `Γ`. -/
theorem trans (h₁ : ∀ θ ∈ Θ, Γ ⊨[p] θ) (h₂ : Θ ⊨[p] φ) : Γ ⊨[p] φ := fun M hM ↦
  h₂ M fun θ hθ ↦ h₁ θ hθ M hM

/-- Consequence transfers along a map of models that preserves and reflects satisfaction. -/
theorem comap {Model' : Type*} {p' : Model' → Formula → Prop} (f : Model' → Model)
    (hf : ∀ M ψ, p' M ψ ↔ p (f M) ψ) (h : Γ ⊨[p] φ) : Γ ⊨[p'] φ := fun M hM ↦
  (hf M φ).2 (h (f M) fun γ hγ ↦ (hf M γ).1 (hM γ hγ))

/-- Consequence over all models holds over any class of them. -/
theorem restrict (K : Model → Prop) (h : Γ ⊨[p] φ) : Γ ⊨[fun M : {M // K M} ↦ p M] φ :=
  h.comap Subtype.val fun _ _ ↦ .rfl

end Entails

end Consequence
