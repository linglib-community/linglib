/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.ProjectivitySignature
public import Linglib.Semantics.Negation.Strength
public import Mathlib.Order.WithBot

/-!
# Strengths of negation as projectivity signatures

Each strength of negation is the function class of a natural-logic signature: the antitone, the
anti-additive and the anti-morphic maps, with Icard's unit conditions. The strength that a
signature realizes is the greatest strength whose class contains it, so the strengths sit among
the signatures as a chain in reverse. A map composed with negation has the strengths dual to the
positive classes of the map.

## Main definitions

* `Negation.Strength.toProjectivitySignature`: the signature whose function class a strength is.
* `NaturalLogic.ProjectivitySignature.negationStrength`: the strength that a signature realizes.
* `Negation.Strength.toProjectivitySignatureEmbedding`: the strengths as a chain among the
  signatures in reverse.

## Main results

* `NaturalLogic.ProjectivitySignature.coe_le_negationStrength_iff`: a signature realizes at least
  a strength exactly when its function class lies in the class of that strength.
* `Negation.Strength.forall_holdsFor_iff_le_antiAdditive`,
  `Negation.Strength.forall_holdsFor_iff_le_weak`: the strengths of a multiplicative map after
  negation, and of negation after a monotone map.

## References

* [zwarts-1998]
* [icard-2012]
* [ladusaw-1979]
-/

@[expose] public section

namespace Negation.Strength

open NaturalLogic

/-- The natural-logic signature whose function class a strength of negation is, an antitone, an
anti-additive or an anti-morphic map with Icard's unit conditions. -/
def toProjectivitySignature : Strength → ProjectivitySignature
  | .weak => .anti
  | .antiAdditive => .antiAdd
  | .antiMorphic => .antiAddMult

end Negation.Strength

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

/-- The strengths as a chain among the signatures in reverse. -/
def toProjectivitySignatureEmbedding : Strengthᵒᵈ ↪o ProjectivitySignature :=
  .ofMapLEIff (fun s ↦ s.ofDual.toProjectivitySignature)
    fun _ _ ↦ toProjectivitySignature_le_toProjectivitySignature

@[simp] theorem toProjectivitySignatureEmbedding_apply (s : Strengthᵒᵈ) :
    toProjectivitySignatureEmbedding s = s.ofDual.toProjectivitySignature := rfl

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
