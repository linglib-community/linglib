/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Strengths of negation

This file defines the strengths of negation a context can carry, Zwarts's hierarchy of weak,
anti-additive and anti-morphic contexts, which are van der Wouden's minimal, regular and classical
negation. A context is weakly negative when it is downward entailing, anti-additive when it also
turns disjunctions into conjunctions, and anti-morphic when it also turns conjunctions into
disjunctions, as clausal negation does. The strengths form a chain.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [ladusaw-1979]
-/

@[expose] public section

namespace Negation

/-- The three strengths of negation, `weak` plain downward entailment, `antiAdditive` adding the
∨→∧ distributivity of *nobody*, and `antiMorphic` the ∧→∨ distributivity of clausal negation. -/
inductive Strength where
  | weak
  | antiAdditive
  | antiMorphic
  deriving DecidableEq, Repr, Fintype

namespace Strength

/-- Rank in the chain `weak < antiAdditive < antiMorphic`. -/
def toNat : Strength → ℕ
  | .weak => 0
  | .antiAdditive => 1
  | .antiMorphic => 2

theorem toNat_injective : Function.Injective toNat := by decide

/-- The Zwarts hierarchy as the linear order `weak < antiAdditive < antiMorphic`. -/
instance : LinearOrder Strength :=
  LinearOrder.lift' toNat toNat_injective

instance : BoundedOrder Strength where
  bot := weak
  bot_le := by decide
  top := antiMorphic
  le_top := by decide

@[simp] theorem bot_eq_weak : (⊥ : Strength) = weak := rfl

@[simp] theorem top_eq_antiMorphic : (⊤ : Strength) = antiMorphic := rfl

@[simp] theorem weak_le (s : Strength) : weak ≤ s := bot_le

@[simp] theorem le_antiMorphic (s : Strength) : s ≤ antiMorphic := le_top

@[simp] theorem le_weak_iff {s : Strength} : s ≤ weak ↔ s = weak := le_bot_iff

end Strength

end Negation
