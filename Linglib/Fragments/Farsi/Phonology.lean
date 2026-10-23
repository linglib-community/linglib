module

public import Linglib.Data.PHOIBLE.Inventories.Persian
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Persian phonemes

This file lists the Persian phonemes that the hiatus data use and gives each its segment.
Modern Persian distinguishes six vowels, front unrounded /i e æ/ against back /u o ɑ/, the
back series rounded except for the variably rounded low vowel, and some two dozen consonants,
among them the glottal stop /ʔ/ that breaks vowel hiatus. The vowels are here with /h tʃ m n ʔ/.
The feature values of a phoneme are not listed. Each phoneme names its glyph in the PHOIBLE
chart, and its segment is the segment of that chart entry.

## Main definitions

* `Farsi.e`, `Farsi.h` and the like: the phonemes, as segments of their chart entries.
* `Farsi.inventory`: the set of them.

## Main results

* `Farsi.subset_pes`: the phonemes are segments of PHOIBLE's Persian inventory.
* `Farsi.isVowel_iff`: the six vowels are the vowels.

## Implementation notes

PHOIBLE's Persian inventory is the Stanford Phonology Archive's, which writes the low front
vowel `a̟` and the affricate `t̠ʃ`, and those are the chart entries taken here. Majidi and
Ternes transcribe the vowel /æ/.

## References

* [majidi-ternes-1991]
* [moran-mccloy-2019]
* [hayes-2009]
* [ariyaee-jurgec-2021]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Farsi

/-! ### Phonemes -/

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The low front vowel /æ/, the glyph `a̟` of the Persian inventory. -/
def æ : Segment := .ofChart .«a̟»

/-- The high back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The mid back rounded vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The low back vowel /ɑ/. -/
def scriptA : Segment := .ofChart .«ɑ»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The voiceless postalveolar affricate /tʃ/. -/
def tesh : Segment := .ofChart .«t̠ʃ»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The glottal stop /ʔ/. -/
def glottalStop : Segment := .ofChart .«ʔ»

/-- The Persian phonemes of the hiatus data, pairwise distinct. -/
def inventory : Finset Segment := ⟨↑[i, e, æ, u, o, scriptA, h, tesh, m, n, glottalStop], by decide⟩

theorem subset_pes : inventory ⊆ Inventories.Persian.pes.segments :=
  Inventory.subset_segments_iff.2 (by decide)

theorem isVowel_iff :
    ∀ x ∈ inventory, x.IsVowel ↔ x ∈ ({i, e, æ, u, o, scriptA} : Finset Segment) := by
  decide

end Farsi
