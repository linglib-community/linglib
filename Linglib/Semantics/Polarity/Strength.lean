/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Basic

/-!
# The Zwarts hierarchy of negative strength

The strengths of negation a context can carry, Zwarts's hierarchy and van der Wouden's minimal,
regular and classical negation, are ordered as the chain `weak < antiAdditive < antiMorphic`. A
context is weakly negative when it is downward entailing, anti-additive when it also turns
disjunctions into conjunctions, and anti-morphic when it also turns conjunctions into
disjunctions, as clausal negation does. Each strength is the function class of a natural-logic
signature (`Negation.Strength.toSignature`), so its semantic content is `Signature.HoldsFor`,
with the unit conditions that keep a constant map from holding every strength, and a signature
realizes a strength through its projection behavior (`Signature.negationStrength`). The forms
that express negation are in `Syntax/Negation`.

## Main declarations

* `Negation.Strength`: the three strengths, a linear order.
* `Negation.Strength.toSignature`: the signature whose function class a strength is.
* `NaturalLogic.Signature.negationStrength`: the strength a signature realizes, `⊥` for a
  signature that is not downward entailing.
* `NaturalLogic.Signature.negationStrength_ne_bot_iff`: a signature realizes a strength exactly
  when it is downward entailing.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [icard-2012]
* [ladusaw-1979]
-/

@[expose] public section

namespace Negation

open NaturalLogic

/-! ### The hierarchy -/

/-- The three strengths of negation, `weak` plain downward entailment, `antiAdditive` adding the
∨→∧ distributivity of *nobody*, and `antiMorphic` the ∧→∨ distributivity of clausal negation. -/
inductive Strength where
  | weak
  | antiAdditive
  | antiMorphic
  deriving DecidableEq, Repr, Fintype

/-- Rank in the chain `weak < antiAdditive < antiMorphic`. -/
def Strength.toNat : Strength → ℕ
  | .weak => 0
  | .antiAdditive => 1
  | .antiMorphic => 2

theorem Strength.toNat_injective : Function.Injective Strength.toNat := by decide

/-- The Zwarts hierarchy as the linear order `weak < antiAdditive < antiMorphic`. -/
instance : LinearOrder Strength :=
  LinearOrder.lift' Strength.toNat Strength.toNat_injective

/-- The natural-logic signature whose function class a strength of negation is, an antitone, an
anti-additive or an anti-morphic map with Icard's unit conditions. -/
def Strength.toSignature : Strength → Signature
  | .weak => .anti
  | .antiAdditive => .antiAdd
  | .antiMorphic => .antiAddMult

/-- A stronger strength is a more specific signature. -/
theorem Strength.toSignature_antitone : Antitone Strength.toSignature := by
  intro a b h; cases a <;> cases b <;> first | exact absurd h (by decide) | decide

end Negation

/-! ### Signatures and strength -/

namespace NaturalLogic.Signature

/-- `negationStrength φ` is the strength of negation the signature `φ` realizes, `⊥` when `φ` is not
downward entailing. It is read off `project`: a signature is downward entailing when it reverses
forward entailment, anti-additive when it also turns `cover` into `alternation`, and anti-morphic
when it also turns `alternation` into `cover`. -/
def negationStrength (φ : Signature) : WithBot Negation.Strength :=
  if project .forward φ != .reverse then ⊥
  else if project .cover φ == .alternation then
    if project .alternation φ == .cover then Negation.Strength.antiMorphic
    else Negation.Strength.antiAdditive
  else Negation.Strength.weak

example : negationStrength .anti = Negation.Strength.weak := rfl
example : negationStrength .antiAdd = Negation.Strength.antiAdditive := rfl
example : negationStrength .antiMult = Negation.Strength.weak := rfl
example : negationStrength .antiAddMult = Negation.Strength.antiMorphic := rfl
example : negationStrength .mono = ⊥ := rfl

/-- A signature realizes a strength of negation exactly when it is downward entailing
([ladusaw-1979]). -/
theorem negationStrength_ne_bot_iff (σ : Signature) : σ.negationStrength ≠ ⊥ ↔ σ.sign = -1 := by
  cases σ <;> decide

theorem negationStrength_toSignature (s : Negation.Strength) :
    s.toSignature.negationStrength = s := by
  cases s <;> rfl

end NaturalLogic.Signature
