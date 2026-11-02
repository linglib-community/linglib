module

public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# English phonemes

This file lists the English phonemes of Hayes's tables and gives each its segment, together with
two of the book's English rules as local rewrite rules, and sorts the beginnings of words by how
they select the form of an article before them. The feature values of a phoneme are not listed
here. Each phoneme names its glyph in the PHOIBLE chart, and its segment is the segment of that
chart entry, so the values are PHOIBLE's.

## Main definitions

* `English.Phonology.p`, `English.Phonology.esh` and the like: the phonemes, as segments of their
  chart entries.
* `English.Phonology.phonemes`, `English.Phonology.inventory`: the phonemes by glyph, and the set
  of them.
* `English.Phonology.transcribe`: the segments of a transcription, a diphthong as two vowels.
* `English.Phonology.preglottalization`, `English.Phonology.postnasalDeletion`: two rules of
  Hayes's.
* `English.Phonology.Onset`, `English.Phonology.Onset.of`: the beginnings of words.

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
The chart has no entries for diphthongs. Hayes writes a diphthong as the two vowels of its
beginning and end, so the diphthongs /aɪ aʊ ɔɪ/ of Table 2.2 are transcribed as two segments, and
/eɪ/, which the table lists among the vowels, is left out; /oʊ/ is the monophthong /o/.

## References

* [hayes-2009]
* [huddleston-pullum-2002]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace English.Phonology

/-! ### Phonemes

The consonants of Hayes's Table 2.1 (p. 21) and the vowels of Table 2.2 (p. 22). -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar stop /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless palatoalveolar affricate /tʃ/. -/
def tesh : Segment := .ofChart .«t̠ʃ»

/-- The voiced palatoalveolar affricate /dʒ/. -/
def dezh : Segment := .ofChart .«d̠ʒ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiced labiodental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The voiceless dental fricative /θ/. -/
def θ : Segment := .ofChart .«θ»

/-- The voiced dental fricative /ð/. -/
def ð : Segment := .ofChart .«ð»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless palatoalveolar fricative /ʃ/. -/
def esh : Segment := .ofChart .«ʃ»

/-- The voiced palatoalveolar fricative /ʒ/. -/
def ezh : Segment := .ofChart .«ʒ»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The velar nasal /ŋ/. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The alveolar approximant /ɹ/. -/
def turnedR : Segment := .ofChart .«ɹ»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The upper high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The lower high front vowel /ɪ/. -/
def smallCapitalI : Segment := .ofChart .«ɪ»

/-- The lower mid front vowel /ɛ/. -/
def epsilon : Segment := .ofChart .«ɛ»

/-- The low front vowel /æ/. -/
def æ : Segment := .ofChart .«æ»

/-- The upper mid central vowel /ə/. -/
def schwa : Segment := .ofChart .«ə»

/-- The lower mid back unrounded vowel /ʌ/. -/
def wedge : Segment := .ofChart .«ʌ»

/-- The low back unrounded vowel /ɑ/. -/
def scriptA : Segment := .ofChart .«ɑ»

/-- The upper high back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The lower high back rounded vowel /ʊ/. -/
def upsilon : Segment := .ofChart .«ʊ»

/-- The upper mid back rounded vowel /oʊ/, as the monophthong /o/. -/
def o : Segment := .ofChart .«o»

/-- The lower mid back rounded vowel /ɔ/. -/
def openO : Segment := .ofChart .«ɔ»

/-- The rhotacized upper mid central vowel /ɚ/. -/
def rightHookSchwa : Segment := .ofChart .«ɚ»

/-- The English phonemes by glyph, in Hayes's transcription. -/
def phonemes : List (String × Segment) :=
  [("p", p), ("b", b), ("t", t), ("d", d), ("k", k), ("ɡ", g), ("tʃ", tesh), ("dʒ", dezh),
    ("f", f), ("v", v), ("θ", θ), ("ð", ð), ("s", s), ("z", z), ("ʃ", esh), ("ʒ", ezh), ("h", h),
    ("m", m), ("n", n), ("ŋ", ŋ), ("l", l), ("w", w), ("ɹ", turnedR), ("j", j), ("i", i),
    ("ɪ", smallCapitalI), ("ɛ", epsilon), ("æ", æ), ("ə", schwa), ("ʌ", wedge), ("ɑ", scriptA),
    ("u", u), ("ʊ", upsilon), ("o", o), ("ɔ", openO), ("ɚ", rightHookSchwa)]

/-- The English phonemes, pairwise distinct. -/
def inventory : Finset Segment :=
  ⟨↑(phonemes.map Prod.snd), by decide⟩

/-- The open front vowel [a], the beginning of the diphthongs /aɪ/ and /aʊ/. -/
def a : Segment := .ofChart .«a»

/-- The diphthongs of Table 2.2 by glyph, each the two vowels of its beginning and end (p. 15). -/
def diphthongs : List (String × List Segment) :=
  [("aɪ", [a, smallCapitalI]), ("aʊ", [a, upsilon]), ("ɔɪ", [openO, smallCapitalI])]

/-- The segments a glyph transcribes: a phoneme's segment, or a diphthong's two vowels. -/
def ofGlyph? (x : String) : Option (List Segment) :=
  ((phonemes.lookup x).map ([·])).orElse fun _ ↦ diphthongs.lookup x

/-- The segments of a transcription, when every glyph is English. -/
def transcribe (xs : List String) : Option (List Segment) :=
  (xs.mapM ofGlyph?).map List.flatten

/-! ### Natural classes -/

/-- The nasals are the complete set of [+nasal] sounds. -/
theorem naturalClass_nasal :
    (Segment.ofSpecs [(.nasal, true)]).naturalClass inventory = {m, n, ŋ} := by
  decide

/-- The voiceless stops /p t k/ are a natural class. -/
theorem isNaturalClass_voicelessStops : IsNaturalClass inventory {p, t, k} := by decide

/-- The glides, liquids and nasals, contiguous on the sonority hierarchy, are a natural
class. -/
theorem isNaturalClass_sonorantConsonants :
    IsNaturalClass inventory {w, j, l, turnedR, m, n, ŋ} := by
  decide

/-- The stops and the liquids, which are not contiguous on the sonority hierarchy, are not a
natural class. -/
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

/-! ### The beginnings of words -/

/-- The beginning of a word, as it selects the form of an article before it: a vowel sound or a
consonant, whatever the spelling ([huddleston-pullum-2002] ch. 18 §6.4, p. 1618). -/
inductive Onset where
  /-- A vowel, as in *an uncle*. -/
  | vowel
  /-- A consonant, the glides among them, as in *a unit* and *a once-in-a-lifetime opportunity*. -/
  | consonant
  deriving DecidableEq, Fintype, Repr

/-- The beginning of a word, read from its first segment; the empty word counts as
`consonant`. -/
def Onset.of : List Segment → Onset
  | x :: _ => if x.IsVowel then .vowel else .consonant
  | [] => .consonant

theorem Onset.of_eq_vowel_iff {w : List Segment} :
    Onset.of w = .vowel ↔ ∃ x ∈ w.head?, x.IsVowel := by
  cases w with
  | nil => simp [Onset.of]
  | cons x w => by_cases hx : x.IsVowel <;> simp [Onset.of, hx]

end English.Phonology
