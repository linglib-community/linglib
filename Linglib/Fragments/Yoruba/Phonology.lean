/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.PHOIBLE.Inventories.Yoruba
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Yoruba vowels

Standard Yoruba has seven oral vowels, /i e ɛ a ɔ o u/, the mid-only tongue-root system of
Casali's typology, analyzed by Archangeli and Pulleyblank: the mid vowels pair, /e o/ [+ATR]
against /ɛ ɔ/ [−ATR], while the high vowels /i u/ are [+ATR] and the low vowel /a/ [−ATR]
without counterparts. Non-high vowels in a word agree in [ATR]. The nasal vowels are not
represented.

The feature values come from the PHOIBLE chart, which codes the tongue-root contrast by
[tense], so a vowel is the segment of its chart entry's tongue-root reading.

## Main definitions

* `Yoruba.vowel`: the segment of a vowel's chart entry, with [tense] read as [ATR].
* `Yoruba.i`, `Yoruba.epsilon` and the like: the seven vowels, and `Yoruba.vowels` the set of
  them.

## Main results

* `Yoruba.subset_yor`: the vowels are those of PHOIBLE's Yoruba inventory.
* `Yoruba.hasValue_atr_iff`: the advanced vowels are /i e o u/.

## References

* [casali-2003]
* [archangeli-pulleyblank-1989]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Yoruba

/-- A vowel is the segment of its chart entry's tongue-root reading. -/
def vowel (m : FeatureMatrix) : Segment := .ofChart m.tenseAsATR

/-- The high front vowel /i/. -/
def i : Segment := vowel .«i»

/-- The advanced mid front vowel /e/. -/
def e : Segment := vowel .«e»

/-- The unadvanced mid front vowel /ɛ/. -/
def epsilon : Segment := vowel .«ɛ»

/-- The low vowel /a/. -/
def a : Segment := vowel .«a»

/-- The unadvanced mid back vowel /ɔ/. -/
def openO : Segment := vowel .«ɔ»

/-- The advanced mid back vowel /o/. -/
def o : Segment := vowel .«o»

/-- The high back vowel /u/. -/
def u : Segment := vowel .«u»

/-- The seven oral vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[i, e, epsilon, a, openO, o, u], by decide⟩

/-- The vowels are those of PHOIBLE's Yoruba inventory. -/
theorem subset_yor : vowels ⊆ Inventories.Yoruba.yor.featureMatrices.image vowel :=
  Inventory.subset_image_featureMatrices_iff.2 (by decide)

/-- The advanced vowels are /i e o u/. -/
theorem hasValue_atr_iff :
    ∀ x ∈ vowels, x.HasValue .atr true ↔ x ∈ ({i, e, o, u} : Finset Segment) := by
  decide

end Yoruba
