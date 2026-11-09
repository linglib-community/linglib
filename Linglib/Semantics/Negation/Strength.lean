/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.ProjectivitySignature

/-!
# Strengths of negation

This file defines the strengths of negation a context can carry, Zwarts's hierarchy of weak,
anti-additive and anti-morphic contexts, which are van der Wouden's minimal, regular and classical
negation. A context is weakly negative when it is downward entailing, anti-additive when it also
turns disjunctions into conjunctions, and anti-morphic when it also turns conjunctions into
disjunctions, as clausal negation does. Each strength is the function class of a natural-logic
signature, and the strength a signature realizes is [the greatest strength whose class contains
it](##NaturalLogic.ProjectivitySignature.coe_le_negationStrength_iff), so that the strengths sit
among the signatures as a chain in reverse.

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
def toProjectivitySignature : Strength → ProjectivitySignature
  | .weak => .anti
  | .antiAdditive => .antiAdd
  | .antiMorphic => .antiAddMult

end Strength

end Negation

/-! ### The strength a signature realizes -/

namespace NaturalLogic.ProjectivitySignature

/-- `negationStrength φ` is the strength of negation the signature `φ` realizes, `⊥` when `φ` is not
downward entailing: weak when its class is antitone, anti-additive when it is also anti-additive,
and anti-morphic when it is also anti-multiplicative. -/
def negationStrength (φ : ProjectivitySignature) : WithBot Negation.Strength :=
  if .antitone ∉ φ.properties then ⊥
  else if .antiAdditive ∈ φ.properties then
    if .antiMultiplicative ∈ φ.properties then Negation.Strength.antiMorphic
    else Negation.Strength.antiAdditive
  else Negation.Strength.weak

/-- A signature realizes at least a strength exactly when its function class lies in the class of
that strength: the strength it realizes is the greatest one whose class contains it. -/
theorem coe_le_negationStrength_iff {σ : ProjectivitySignature} {s : Negation.Strength} :
    (s : WithBot Negation.Strength) ≤ σ.negationStrength ↔ σ ≤ s.toProjectivitySignature := by
  revert σ s; decide

@[simp]
theorem negationStrength_toProjectivitySignature (s : Negation.Strength) :
    s.toProjectivitySignature.negationStrength = s := by
  cases s <;> rfl

/-- A signature realizes a strength of negation exactly when it is downward entailing
([ladusaw-1979]). -/
theorem negationStrength_ne_bot_iff (σ : ProjectivitySignature) :
    σ.negationStrength ≠ ⊥ ↔ σ.sign = -1 := by
  cases σ <;> decide

end NaturalLogic.ProjectivitySignature

namespace Negation.Strength

open NaturalLogic

/-- A stronger strength is a more specific signature. -/
@[simp]
theorem toProjectivitySignature_le_toProjectivitySignature {s t : Strength} :
    s.toProjectivitySignature ≤ t.toProjectivitySignature ↔ t ≤ s := by
  simpa using (ProjectivitySignature.coe_le_negationStrength_iff
    (σ := s.toProjectivitySignature) (s := t)).symm

theorem toProjectivitySignature_antitone : Antitone toProjectivitySignature :=
  fun _ _ h ↦ toProjectivitySignature_le_toProjectivitySignature.2 h

/-! ### The strength of a negation composite

A map composed with negation has the strengths dual to the positive classes of the map, since
negation is its own inverse among the signatures. -/

section Composite

open ProjectivitySignature

variable {ι : Type*} {α γ β : ι → Type*} [∀ i, Lattice (α i)] [∀ i, BoundedOrder (α i)]
  [∀ i, BooleanAlgebra (γ i)] [∀ i, Lattice (β i)] [∀ i, BoundedOrder (β i)] {s : Strength}

/-- Maps that are multiplicative maps after negation, not all of them additive, hold exactly the
strengths up to anti-additive. -/
theorem forall_holdsFor_iff_le_antiAdditive {f g : ∀ i, γ i → β i}
    (hfg : ∀ i, f i = g i ∘ compl) (hg : ∀ i, mult.HoldsFor (g i))
    (hn : ∃ i, ¬ additive.HoldsFor (g i)) :
    (∀ i, s.toProjectivitySignature.HoldsFor (f i)) ↔ s ≤ antiAdditive := by
  simp only [hfg, holdsFor_comp_compl_iff]
  cases s
  · exact iff_of_true (fun i ↦ (hg i).of_le (by decide)) (by decide)
  · exact iff_of_true (fun i ↦ (hg i).of_le (by decide)) le_rfl
  · exact iff_of_false (fun h ↦ hn.elim fun i hi ↦ hi ((h i).of_le (by decide))) (by decide)

/-- Negation after monotone maps, not all of them additive, holds exactly weak strength. -/
theorem forall_holdsFor_iff_le_weak {f g : ∀ i, α i → γ i} (hfg : ∀ i, f i = compl ∘ g i)
    (hg : ∀ i, mono.HoldsFor (g i)) (hn : ∃ i, ¬ additive.HoldsFor (g i)) :
    (∀ i, s.toProjectivitySignature.HoldsFor (f i)) ↔ s ≤ weak := by
  simp only [hfg, holdsFor_compl_comp_iff]
  cases s
  · exact iff_of_true (fun i ↦ (hg i).of_le (by decide)) le_rfl
  all_goals
    exact iff_of_false (fun h ↦ hn.elim fun i hi ↦ hi ((h i).of_le (by decide))) (by decide)

end Composite

end Negation.Strength
