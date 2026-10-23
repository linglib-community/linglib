/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Agreement.Phi
public import Linglib.Morphology.Word.Basic

/-!
# φ-agreement between word tokens

A word's φ-features are the agreement dimensions of its features, so two words agree when those
bundles are compatible. Agreement is reflexive and symmetric but not transitive, since an
unspecified dimension agrees with every value.

## Main results

* `Morphology.Word.not_isTrans_agree`: agreement between words is not transitive.
-/

@[expose] public section

namespace Morphology

/-- A word bears the agreement dimensions of its features. -/
instance Word.instHasPhi : HasPhi Word := ⟨fun w ↦ phi w.features⟩

theorem Word.not_isTrans_agree : ¬ IsTrans Word HasPhi.Agree := fun ⟨h⟩ ↦
  absurd
    (h ⟨"she", .PRON, Features.of (person := some .third) (number := some .singular)
          (gender := some .feminine)⟩
       ⟨"they", .PRON, Features.of (person := some .third)⟩
       ⟨"he", .PRON, Features.of (person := some .third) (number := some .singular)
          (gender := some .masculine)⟩
       (by decide) (by decide))
    (by decide)

/-- Reflexivity is not an agreement feature: a reflexive-marked token agrees with an unmarked
one. -/
example : HasPhi.Agree (⟨"sich", .PRON, Features.of (reflex := some ())⟩ : Word)
    (⟨"Kind", .NOUN, ⊥⟩ : Word) := by
  decide

end Morphology
