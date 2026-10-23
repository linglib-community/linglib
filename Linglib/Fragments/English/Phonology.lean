module

public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# English phonemes

This file lists the English phonemes that Hayes's textbook examples use and gives each its
segment, together with two of the book's English rules as local rewrite rules. The feature
values of a phoneme are not listed here. Each phoneme names its glyph in the PHOIBLE chart,
and its segment is the segment of that chart entry, so the values are PHOIBLE's.

## Main definitions

* `English.Phonology.p`, `English.Phonology.esh` and the like: the phonemes, as segments of their
  chart entries.
* `English.Phonology.inventory`: the set of them.
* `English.Phonology.preglottalization`, `English.Phonology.postnasalDeletion`: two rules of
  Hayes's.

## Main results

* `English.Phonology.naturalClass_nasal`, `English.Phonology.isNaturalClass_voicelessStops`: Hayes's
  examples of natural classes, the nasals and /p t k/.
* `English.Phonology.isNaturalClass_sonorantConsonants`,
  `English.Phonology.not_isNaturalClass_stops_liquids`: the sonorant consonants, contiguous in
  sonority, are a natural class, and the stops with the liquids are not.

## Implementation notes

The transcription is Hayes's, with plain /p t k/. PHOIBLE's English inventories write the
voiceless stops aspirated, so no inventory contains these glyphs, and membership in one is not
stated. English /ɹ/ is the chart's `ɹ`, which is [−consonantal] and so a glide in sonority.

## References

* [hayes-2009]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace English.Phonology

/-! ### Phonemes -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiced velar stop /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiced postalveolar affricate /dʒ/. -/
def dezh : Segment := .ofChart .«d̠ʒ»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The velar nasal /ŋ/. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiced labiodental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiceless dental fricative /θ/. -/
def θ : Segment := .ofChart .«θ»

/-- The voiceless postalveolar fricative /ʃ/. -/
def esh : Segment := .ofChart .«ʃ»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The alveolar approximant /ɹ/. -/
def turnedR : Segment := .ofChart .«ɹ»

/-- The low front vowel /æ/. -/
def æ : Segment := .ofChart .«æ»

/-- The lax high front vowel /ɪ/. -/
def smallCapitalI : Segment := .ofChart .«ɪ»

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The mid back unrounded vowel /ʌ/. -/
def wedge : Segment := .ofChart .«ʌ»

/-- The mid back rounded vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The mid central vowel /ə/. -/
def schwa : Segment := .ofChart .«ə»

/-- The English phonemes of the examples, pairwise distinct. -/
def inventory : Finset Segment :=
  ⟨↑[p, t, k, b, d, g, dezh, m, n, ŋ, f, v, s, θ, esh, l, w, turnedR, æ, smallCapitalI, i, wedge,
    o, schwa], by decide⟩

/-! ### Natural classes -/

theorem naturalClass_nasal :
    (Segment.ofSpecs [(.nasal, true)]).naturalClass inventory = {m, n, ŋ} := by
  decide

theorem isNaturalClass_voicelessStops : IsNaturalClass inventory {p, t, k} := by decide

theorem isNaturalClass_sonorantConsonants :
    IsNaturalClass inventory {w, l, turnedR, m, n, ŋ} := by
  decide

theorem not_isNaturalClass_stops_liquids :
    ¬ IsNaturalClass inventory {p, t, k, b, d, g, l, turnedR} := by
  decide

/-! ### Rules -/

/-- Preglottalization glottalizes a voiceless stop word-finally,
`[−cont, −voice] → [+c.g.] / __ ]word`. -/
def preglottalization : Rule where
  target := Segment.ofSpecs
    [(Phonology.Feature.continuant, false), (Phonology.Feature.voice, false)]
  effect := .changeFeatures (Segment.ofSpecs [(Phonology.Feature.constrGlottis, true)])
  rightContext := [.wordBoundary]

/-- Postnasal /t/ deletion removes a voiceless coronal stop between a nasal and a vowel,
`[−cont, +cor, +ant, −voice] → ∅ / [+nasal] __ [+syll]`. -/
def postnasalDeletion : Rule where
  target := Segment.ofSpecs
    [(Phonology.Feature.continuant, false), (Phonology.Feature.coronal, true),
     (Phonology.Feature.anterior, true), (Phonology.Feature.voice, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(Phonology.Feature.nasal, true)])]
  rightContext := [.seg (Segment.ofSpecs [(Phonology.Feature.syllabic, true)])]

end English.Phonology
