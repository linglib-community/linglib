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
the signatures as a chain in reverse. The class of the anti-additive signature is smaller than
the anti-additive maps, since it also requires that `⊤` be sent to `⊥`; the classes of the weak and
the anti-morphic signature are the monotone decreasing and the antimorphic maps.

## Main definitions

* `Negation.Strength.toProjectivitySignature`: the signature whose function class a strength is.
* `NaturalLogic.ProjectivitySignature.negationStrength`: the strength that a signature realizes.
* `Negation.Strength.toProjectivitySignatureEmbedding`: the strengths as a chain among the
  signatures in reverse.

## Main results

* `NaturalLogic.ProjectivitySignature.coe_le_negationStrength_iff`: a signature realizes at least
  a strength exactly when its function class lies in the class of that strength.
* `Negation.HasStrength.of_toProjectivitySignature`: a map in the function class of a
  strength has the strength.
* `Negation.hasStrength_antimorphic_iff_holdsFor`: the antimorphic maps are those of the
  anti-morphism signature.

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
  | .monotoneDecreasing => .anti
  | .antiAdditive => .antiAdd
  | .antimorphic => .antiAddMult

end Negation.Strength

/-! ### The strength a signature realizes -/

namespace NaturalLogic.ProjectivitySignature

/-- `negationStrength φ` is the strength of negation the signature `φ` realizes, `⊥` when `φ` is not
downward entailing: weak when its class is antitone, anti-additive when it is also anti-additive,
and anti-morphic when it is also anti-multiplicative. -/
def negationStrength (φ : ProjectivitySignature) : WithBot Negation.Strength :=
  if .antitone ∉ φ.properties then ⊥
  else if .antiAdditive ∈ φ.properties then
    if .antiMultiplicative ∈ φ.properties then Negation.Strength.antimorphic
    else Negation.Strength.antiAdditive
  else Negation.Strength.monotoneDecreasing

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

end Negation.Strength

namespace Negation

open NaturalLogic Strength

/-- A map in the function class of a strength has the strength. -/
theorem HasStrength.of_toProjectivitySignature {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
    {s : Strength} {f : α → β} (h : s.toProjectivitySignature.HoldsFor f) : HasStrength f s := by
  cases s
  · exact ProjectivitySignature.holdsFor_anti_iff.1 h
  · exact (ProjectivitySignature.holdsFor_antiAdd_iff.1 h).1
  · obtain ⟨⟨ha, ht⟩, hm, hb⟩ := ProjectivitySignature.holdsFor_antiAddMult_iff.1 h
    exact ⟨ha, (IsAntiAdditive.map_compl_iff ha).2 ⟨ht, hm, hb⟩⟩

/-- The antimorphic maps are the maps in the function class of the anti-morphism signature. -/
theorem hasStrength_antimorphic_iff_holdsFor {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
    {f : α → β} :
    HasStrength f antimorphic ↔ ProjectivitySignature.antiAddMult.HoldsFor f :=
  ⟨fun h ↦ ProjectivitySignature.holdsFor_antiAddMult_iff.2
      (have hc := (IsAntiAdditive.map_compl_iff (f := f) h.1).1 h.2
       ⟨⟨h.1, hc.1⟩, hc.2.1, hc.2.2⟩),
    HasStrength.of_toProjectivitySignature (s := antimorphic)⟩

end Negation
