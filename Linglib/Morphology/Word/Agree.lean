/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Bundle
public import Linglib.Morphology.Word.Basic

/-!
# φ-agreement between word tokens

A word bears the agreement bundle of its features, `Morphology.Word.agreement`. Two words agree
in φ-features when the indices of their bundles (`Agreement.Bundle.index`) are compatible,
compatibility and not identity of values: controller and target
each contribute partial information, and a clash of values is a failure of unification
[shieber-1986] [corbett-2006]. The relation is not transitive
(`Morphology.Word.not_isTrans_compat_index`), since an unspecified dimension agrees with every
value, and it does not compare case, so a pronoun agrees with an antecedent of another case.

## References

* [corbett-2006]
* [shieber-1986]
-/

@[expose] public section

namespace Morphology

/-- The agreement bundle of a word, that of its features. -/
def Word.agreement (w : Word) : Agreement.Bundle := .ofFeatures w.features

/-- Agreement between words is not transitive: underspecified *they* agrees with both *she* and
*he*, which disagree. -/
theorem Word.not_isTrans_compat_index :
    ¬ IsTrans Word fun v w ↦ Compat v.agreement.index w.agreement.index := fun ⟨h⟩ ↦
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
example : Compat
    (⟨"she", .PRON, Features.of (person := some .third) (number := some .singular)
      (gender := some .Fem) (case := some .nom)⟩ : Word).agreement.index
    (⟨"her", .PRON, Features.of (person := some .third) (number := some .singular)
      (gender := some .Fem) (case := some .acc)⟩ : Word).agreement.index := by
  decide

/-- Reflexivity is not an agreement feature: a reflexive-marked token agrees with an unmarked
one. -/
example : Compat (⟨"sich", .PRON, Features.of (reflex := some ())⟩ : Word).agreement.index
    (⟨"Kind", .NOUN, ⊥⟩ : Word).agreement.index := by
  decide

end Morphology
