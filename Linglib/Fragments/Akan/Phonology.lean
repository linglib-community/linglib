module

public import Linglib.Data.PHOIBLE.Inventories.Akan
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Segmental.FeatureClass

/-!
# Akan segments

This file lists the vowels of Akan as segments, together with the two consonants of its
velar–palatal alternation. Akan has nine vowels, /i ɪ e ɛ a ɔ o ʊ u/, which Dolphyne
groups into an advanced set /i e o u/ and an unadvanced set /ɪ ɛ a ɔ ʊ/ that do not mix
within a word, the tongue-root harmony Stewart identified; in Casali's typology the
inventory is a five-height system, with the low vowel the only one lacking a partner. In
Akuapem and Asante a tenth quality, the advanced variant of /a/ before syllables with
/i u/, joins the advanced set; it is not represented here. Velar stops become corono-dorsal
palatal affricates before front vowels, the alternation McCarthy and Prince's account of
Akan reduplication turns on.

The feature values come from the PHOIBLE chart. The chart codes the two vowel sets by
[tense] and marks every plain vowel [−ATR], where the Akan literature has [ATR] carry the
contrast, so a vowel is the segment of its chart entry's tongue-root reading, which takes the
[tense] value as the [ATR] value and drops [tense]. The chart omits the palatal affricate,
whose values are contours, and its segment is the velar stop's with the features McCarthy and
Prince's corono-dorsal analysis adds.

## Main definitions

* `Akan.vowel`: the segment of a vowel's chart entry, with [tense] read as [ATR].
* `Akan.i`, `Akan.smallCapitalI` and the like: the nine vowels, and `Akan.vowels` the set of
  them.
* `Akan.k`, `Akan.tcCurl`: the velar stop and its palatalized output.

## Main results

* `Akan.subset_aka`: the vowels are those of PHOIBLE's Akan inventory.
* `Akan.vowel_apply`: a vowel has the chart's values off [ATR] and [tense].
* `Akan.hasValue_atr_iff`: the advanced vowels are /i e o u/.
* `Akan.restrict_tcCurl_eq_k`: the affricate has the stop's values off the four features
  palatalization writes.

## References

* [dolphyne-1988]
* [stewart-1967]
* [casali-2003]
* [mccarthy-prince-1995]
* [hayes-2009]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Akan

/-! ### Vowels -/

/-- A vowel is the segment of its chart entry's tongue-root reading. The low vowel, which the
chart leaves without [tense], keeps the chart's [−ATR]. -/
def vowel (m : FeatureMatrix) : Segment := .ofChart m.tenseAsATR

/-- A vowel has the chart's values off [ATR] and [tense]. -/
theorem vowel_apply (m : FeatureMatrix) {f : Phonology.Feature} (ha : f ≠ .atr)
    (ht : f ≠ .tense) : vowel m f = m.toSegment f := by
  rw [vowel, Segment.ofChart_eq_toSegment, m.toSegment_tenseAsATR_of_ne ha ht]

/-- The advanced high front vowel /i/. -/
def i : Segment := vowel .«i»

/-- The advanced mid front vowel /e/. -/
def e : Segment := vowel .«e»

/-- The advanced mid back vowel /o/. -/
def o : Segment := vowel .«o»

/-- The advanced high back vowel /u/. -/
def u : Segment := vowel .«u»

/-- The unadvanced high front vowel /ɪ/. -/
def smallCapitalI : Segment := vowel .«ɪ»

/-- The unadvanced mid front vowel /ɛ/. -/
def epsilon : Segment := vowel .«ɛ»

/-- The low vowel /a/, which has no advanced partner. -/
def a : Segment := vowel .«a»

/-- The unadvanced mid back vowel /ɔ/. -/
def openO : Segment := vowel .«ɔ»

/-- The unadvanced high back vowel /ʊ/. -/
def upsilon : Segment := vowel .«ʊ»

/-- The nine vowels, pairwise distinct. -/
def vowels : Finset Segment :=
  ⟨↑[i, e, o, u, smallCapitalI, epsilon, a, openO, upsilon], by decide⟩

/-- The vowels are those of PHOIBLE's Akan inventory. -/
theorem subset_aka : vowels ⊆ Inventories.Akan.aka.featureMatrices.image vowel :=
  Inventory.subset_image_featureMatrices_iff.2 (by decide)

/-- Dolphyne's advanced set is /i e o u/. -/
theorem hasValue_atr_iff :
    ∀ x ∈ vowels, x.HasValue .atr true ↔ x ∈ ({i, e, o, u} : Finset Segment) := by
  decide

/-! ### The velar–palatal alternation -/

/-- The features palatalization writes on the velar stop. -/
def palatalized : Segment :=
  Segment.ofSpecs [(.coronal, true), (.anterior, false), (.distributed, true),
    (.delayedRelease, true)]

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiceless palatal affricate /tɕ/ that the stop becomes before a front vowel, `tcCurl`
being the name of the symbol tɕ. It keeps the stop's values, [+dorsal] among them, and adds
[+coronal, −anterior, +distributed] with delayed release, so it is a corono-dorsal complex
segment. -/
def tcCurl : Segment := .ofChart .«k» palatalized

/-- The affricate has the stop's values off the features palatalization writes. -/
theorem restrict_tcCurl_eq_k :
    Segment.restrict ({.coronal, .anterior, .distributed, .delayedRelease}ᶜ) tcCurl =
      Segment.restrict ({.coronal, .anterior, .distributed, .delayedRelease}ᶜ) k := by
  decide

theorem k_tcCurl_coronal :
    k.HasValue .coronal false ∧ tcCurl.HasValue .coronal true := by
  decide

theorem tcCurl_isComplex : tcCurl.IsComplex := by decide

theorem smallCapitalI_front_a_not_front :
    smallCapitalI.HasValue .front true ∧ a.HasValue .front false := by
  decide

end Akan
