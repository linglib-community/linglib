/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# German phonemes

This file lists the German phonemes of Kohler's illustration of the IPA and gives each its
segment, the segment of its glyph in the PHOIBLE chart, together with the transcription that
reads a string of glyphs as segments. The palatal and velar fricatives are allophones of one
phoneme /x/, and the glottal stop is predictable, so neither is a phoneme.

## Implementation notes

* The plosives are Kohler's plain /p t k/, aspirated by convention except after a fricative of
  the same word or before a syllabic nasal, so membership in PHOIBLE's German inventory, which
  writes them aspirated and the rhotic as /ʀ/, is not stated.
* A segment carries no length, so the long /ɛː aː/ are transcribed as two of their vowel, the
  string `Prosody.Syllable.ofLongVowel` yields, and the diphthongs /aɪ ɔɪ aʊ/ as the two vowels
  of their beginning and end. The close vowels, longer than their open partners by convention,
  are single segments.

## References

* [kohler-1990]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology

namespace German.Phonology

/-! ### Phonemes -/

/-- The voiceless bilabial plosive /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiced bilabial plosive /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiceless alveolar plosive /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiced alveolar plosive /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiceless velar plosive /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar plosive /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

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

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless postalveolar fricative /ʃ/. -/
def esh : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar fricative /ʒ/. -/
def ezh : Segment := .ofChart .«ʒ»

/-- The voiceless velar fricative /x/, realized as [ç] after a front vowel or a consonant and
morpheme-initially, as [χ] after a low back vowel and as [x] after a high or mid back vowel. -/
def x : Segment := .ofChart .«x»

/-- The voiced uvular fricative /ʁ/. -/
def invertedSmallCapitalR : Segment := .ofChart .«ʁ»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The palatal approximant /j/. -/
def j : Segment := .ofChart .«j»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The close front unrounded vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The near-close front unrounded vowel /ɪ/. -/
def smallCapitalI : Segment := .ofChart .«ɪ»

/-- The close-mid front unrounded vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The open-mid front unrounded vowel /ɛ/. -/
def epsilon : Segment := .ofChart .«ɛ»

/-- The close front rounded vowel /y/. -/
def y : Segment := .ofChart .«y»

/-- The near-close front rounded vowel /ʏ/. -/
def smallCapitalY : Segment := .ofChart .«ʏ»

/-- The close-mid front rounded vowel /ø/. -/
def ø : Segment := .ofChart .«ø»

/-- The open-mid front rounded vowel /œ/. -/
def œ : Segment := .ofChart .«œ»

/-- The open vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The mid central vowel /ə/. -/
def schwa : Segment := .ofChart .«ə»

/-- The close back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The near-close back rounded vowel /ʊ/. -/
def upsilon : Segment := .ofChart .«ʊ»

/-- The close-mid back rounded vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The open-mid back rounded vowel /ɔ/. -/
def openO : Segment := .ofChart .«ɔ»

/-- The German phonemes by glyph, in Kohler's transcription, the long vowels aside. -/
def phonemes : List (String × Segment) :=
  [("p", p), ("b", b), ("t", t), ("d", d), ("k", k), ("ɡ", g), ("m", m), ("n", n), ("ŋ", ŋ),
    ("f", f), ("v", v), ("s", s), ("z", z), ("ʃ", esh), ("ʒ", ezh), ("x", x),
    ("ʁ", invertedSmallCapitalR), ("h", h), ("j", j), ("l", l), ("i", i), ("ɪ", smallCapitalI),
    ("e", e), ("ɛ", epsilon), ("y", y), ("ʏ", smallCapitalY), ("ø", ø), ("œ", œ), ("a", a),
    ("ə", schwa), ("u", u), ("ʊ", upsilon), ("o", o), ("ɔ", openO)]

/-- The segments of the German phonemes, pairwise distinct. -/
def inventory : Finset Segment :=
  ⟨↑(phonemes.map Prod.snd), by decide⟩

/-- The long vowels and the diphthongs by glyph, a long vowel as two of its vowel and a
diphthong as the vowels of its beginning and end. -/
def vowelSequences : List (String × List Segment) :=
  [("ɛː", [epsilon, epsilon]), ("aː", [a, a]), ("aɪ", [a, smallCapitalI]),
    ("ɔɪ", [openO, smallCapitalI]), ("aʊ", [a, upsilon])]

/-- The segments a glyph transcribes. -/
def ofGlyph? (c : String) : Option (List Segment) :=
  ((phonemes.lookup c).map ([·])).orElse fun _ ↦ vowelSequences.lookup c

/-- The segments of a transcription, when every glyph is German. -/
def transcribe (cs : List String) : Option (List Segment) :=
  (cs.mapM ofGlyph?).map List.flatten

end German.Phonology
