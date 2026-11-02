/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Signature

/-!
# Strengths of negation

This file defines the strengths of negation a context can carry, Zwarts's hierarchy of weak,
anti-additive and anti-morphic contexts, which are van der Wouden's minimal, regular and classical
negation. A context is weakly negative when it is downward entailing, anti-additive when it also
turns disjunctions into conjunctions, and anti-morphic when it also turns conjunctions into
disjunctions, as clausal negation does. Each strength is the function class of a natural-logic
signature, and the strength a signature realizes is [the greatest strength whose class contains
it](##NaturalLogic.Signature.coe_le_negationStrength_iff), so that the strengths sit among the
signatures as a chain in reverse.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [icard-2012]
* [ladusaw-1979]
-/

@[expose] public section

namespace Negation

open NaturalLogic

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

/-- The natural-logic signature whose function class a strength of negation is, an antitone, an
anti-additive or an anti-morphic map with Icard's unit conditions. -/
def toSignature : Strength → Signature
  | .weak => .anti
  | .antiAdditive => .antiAdd
  | .antiMorphic => .antiAddMult

end Strength

end Negation

/-! ### The strength a signature realizes -/

namespace NaturalLogic.Signature

/-- `negationStrength φ` is the strength of negation the signature `φ` realizes, `⊥` when `φ` is not
downward entailing: weak when its class is antitone, anti-additive when it is also anti-additive,
and anti-morphic when it is also anti-multiplicative. -/
def negationStrength (φ : Signature) : WithBot Negation.Strength :=
  if .antitone ∉ φ.properties then ⊥
  else if .antiAdditive ∈ φ.properties then
    if .antiMultiplicative ∈ φ.properties then Negation.Strength.antiMorphic
    else Negation.Strength.antiAdditive
  else Negation.Strength.weak

/-- A signature realizes at least a strength exactly when its function class lies in the class of
that strength: the strength it realizes is the greatest one whose class contains it. -/
theorem coe_le_negationStrength_iff {σ : Signature} {s : Negation.Strength} :
    (s : WithBot Negation.Strength) ≤ σ.negationStrength ↔ σ ≤ s.toSignature := by
  revert σ s; decide

@[simp]
theorem negationStrength_toSignature (s : Negation.Strength) :
    s.toSignature.negationStrength = s := by
  cases s <;> rfl

/-- A signature realizes a strength of negation exactly when it is downward entailing
([ladusaw-1979]). -/
theorem negationStrength_ne_bot_iff (σ : Signature) : σ.negationStrength ≠ ⊥ ↔ σ.sign = -1 := by
  cases σ <;> decide

end NaturalLogic.Signature

namespace Negation.Strength

open NaturalLogic

/-- A stronger strength is a more specific signature. -/
@[simp]
theorem toSignature_le_toSignature {s t : Strength} : s.toSignature ≤ t.toSignature ↔ t ≤ s := by
  simpa using (Signature.coe_le_negationStrength_iff (σ := s.toSignature) (s := t)).symm

theorem toSignature_antitone : Antitone toSignature := fun _ _ h ↦ toSignature_le_toSignature.2 h

end Negation.Strength
