/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.HasPhi
public import Linglib.Morphology.Word.Basic

/-!
# φ-agreement between word tokens

A word bears the agreement bundle of its features, so two words agree when their bundles are
compatible in person, number and gender. Agreement between words is not transitive
(`Morphology.Word.not_isTrans_agree`), since an unspecified dimension agrees with every value.

## References

* [corbett-2006]
-/

@[expose] public section

namespace Morphology

/-- A word bears the agreement dimensions of its features. -/
instance Word.instHasPhi : HasPhi Word := ⟨fun w ↦ phi w.features⟩

/-- Agreement between words is not transitive: underspecified *they* agrees with both *she* and
*he*, which disagree. -/
theorem Word.not_isTrans_agree : ¬ IsTrans Word HasPhi.Agree := fun ⟨h⟩ ↦
  absurd
    (h ⟨"she", .PRON, Features.of (person := some .third) (number := some .singular)
          (gender := some .Fem)⟩
       ⟨"they", .PRON, Features.of (person := some .third)⟩
       ⟨"he", .PRON, Features.of (person := some .third) (number := some .singular)
          (gender := some .Masc)⟩
       (by decide) (by decide))
    (by decide)

/-- Case is not a φ-feature: nominative *she* agrees with accusative *her*, which can be its
antecedent. -/
example : HasPhi.Agree
    (⟨"she", .PRON, Features.of (person := some .third) (number := some .singular)
      (gender := some .Fem) (case := some .nom)⟩ : Word)
    (⟨"her", .PRON, Features.of (person := some .third) (number := some .singular)
      (gender := some .Fem) (case := some .acc)⟩ : Word) := by
  decide

/-- Reflexivity is not an agreement feature: a reflexive-marked token agrees with an unmarked
one. -/
example : HasPhi.Agree (⟨"sich", .PRON, Features.of (reflex := some ())⟩ : Word)
    (⟨"Kind", .NOUN, ⊥⟩ : Word) := by
  decide

end Morphology
