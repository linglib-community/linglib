module

public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Segmental.Sonority

/-!
# Latin phonemes

This file lists the phonemes of Classical Latin and gives each its segment. Cser's synchronic
phonology of the language is the source for the inventory: five vowel qualities, six oral
stops, the voiceless fricatives /f s/, the nasals /m n/, the liquids /l r/, and the glides /j/
and /w/, written ⟨i⟩ and ⟨v⟩ before a vowel. The feature values of a phoneme are not listed
here. Each phoneme names its glyph in the PHOIBLE chart, and its segment is the segment of that
chart entry, so the values are PHOIBLE's.

## Main definitions

* `Latin.a`, `Latin.p` and the like: the phonemes, as segments of their chart entries.
* `Latin.inventory`: the set of them.

## Main results

* `Latin.isVowel_iff`, `Latin.ofSegment_eq_nasal_iff`, `Latin.ofSegment_eq_liquid_iff`,
  `Latin.ofSegment_eq_glide_iff`: the
  vowels and the sonorant consonants fall in their sonority classes.

## Implementation notes

Vowel length is prosodic. Hayes treats duration as a property of the syllable, the feature
system has no [long], and a long vowel is two morae, so only the five qualities are phonemes
here. Clear and dark /l/ are positional variants of the one /l/, which the chart leaves
unspecified for [back], as Sen's analysis of the variants requires. Both glides are
[−consonantal] and [+dorsal], [w] also [+labial], as in the chart.

## TODO

* The labio-velars /kʷ/ and /gʷ/, which the chart omits as contour-valued, the rare /h/ and
  /y/, and the diphthongs.

## References

* [cser-2020]
* [sen-2015]
* [hayes-2009]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Latin

/-! ### Phonemes -/

/-- The low vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The mid back rounded vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The high back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

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

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The alveolar trill /r/. -/
def r : Segment := .ofChart .«r»

/-- The labial-velar glide /w/, orthographic ⟨v⟩. -/
def w : Segment := .ofChart .«w»

/-- The palatal glide /j/, orthographic ⟨i⟩ before a vowel and ⟨e⟩ in ⟨ae⟩ and ⟨oe⟩. -/
def j : Segment := .ofChart .«j»

/-- The phonemes of Classical Latin, pairwise distinct. -/
def inventory : Finset Segment :=
  ⟨↑[a, e, i, o, u, p, b, t, d, k, g, f, s, m, n, l, r, w, j], by decide⟩

theorem isVowel_iff : ∀ x ∈ inventory, x.IsVowel ↔ x ∈ ({a, e, i, o, u} : Finset Segment) := by
  decide

theorem ofSegment_eq_nasal_iff :
    ∀ x ∈ inventory, Sonority.ofSegment x = .nasal ↔ x = m ∨ x = n := by
  decide

theorem ofSegment_eq_liquid_iff :
    ∀ x ∈ inventory, Sonority.ofSegment x = .liquid ↔ x = l ∨ x = r := by
  decide

theorem ofSegment_eq_glide_iff :
    ∀ x ∈ inventory, Sonority.ofSegment x = .glide ↔ x = w ∨ x = j := by
  decide

end Latin
