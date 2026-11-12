module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Shiwilu segments

The consonants and vowels of Shiwilu (Glottocode jebe1250), a Kawapanan language of the Peruvian
Amazon, as [vasquez-aguilar-etal-2026] tabulates them: eighteen consonants, voicing contrasting
in none, and four vowels, the peripheral /i u a/ and the interior /ɘ/, with no contrast in length
or nasality.

The feature values come from the PHOIBLE chart. The chart's labialized velar is [+round] with no
[labial] value, which PHOIBLE gives as a contour; the glottalized tap /ˀɾ/ takes the chart's
glottalized tap, whose matrix does not record that the glottalization precedes the closure.
PHOIBLE's two inventories of the language, from UPSID and SAPhon, differ from this table: neither
has /kʷ/, and SAPhon writes the interior vowel as /ə/. They are not used here.

## Main definitions

* `Shiwilu.p`, `Shiwilu.«kʷ»`, `Shiwilu.«ˀɾ»`, …: the consonants; `Shiwilu.consonants`.
* `Shiwilu.i`, `Shiwilu.«ɘ»`, …: the vowels; `Shiwilu.vowels`.
* `Shiwilu.inventory`: the phonemes.

## References

* [vasquez-aguilar-etal-2026]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Shiwilu

/-! ### Consonants -/

/-- /p/. -/
def p : Segment := .ofChart .«p»

/-- /t/. -/
def t : Segment := .ofChart .«t»

/-- /k/. -/
def k : Segment := .ofChart .«k»

/-- /kʷ/, the labialized velar plosive. -/
def «kʷ» : Segment := .ofChart .«kʷ»

/-- /ʔ/, the glottal stop. -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- /t͡ʃ/, the palato-alveolar affricate. -/
def «t͡ʃ» : Segment := .ofChart .«t̠ʃ»

/-- /m/. -/
def m : Segment := .ofChart .«m»

/-- /n/. -/
def n : Segment := .ofChart .«n»

/-- /ɲ/, the palatal nasal. -/
def «ɲ» : Segment := .ofChart .«ɲ»

/-- /s/. -/
def s : Segment := .ofChart .«s»

/-- /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- /ɾ/, the alveolar tap. -/
def «ɾ» : Segment := .ofChart .«ɾ»

/-- /ˀɾ/, the glottalized tap. -/
def «ˀɾ» : Segment := .ofChart .«ɾˀ»

/-- /l/. -/
def l : Segment := .ofChart .«l»

/-- /ʎ/, the palatal lateral. -/
def «ʎ» : Segment := .ofChart .«ʎ»

/-- /w/. -/
def w : Segment := .ofChart .«w»

/-- /ð̞/, the dental approximant, written ⟨d⟩. -/
def «ð̞» : Segment := .ofChart .«ð̞»

/-- /j/. -/
def j : Segment := .ofChart .«j»

/-- The consonants (Table 1 of [vasquez-aguilar-etal-2026]). -/
def consonants : Finset Segment :=
  ⟨↑[p, t, k, «kʷ», «ʔ», «t͡ʃ», m, n, «ɲ», s, «ʃ», «ɾ», «ˀɾ», l, «ʎ», w, «ð̞», j], by decide⟩

/-! ### Vowels -/

/-- /i/. -/
def i : Segment := .ofChart .«i»

/-- /u/. -/
def u : Segment := .ofChart .«u»

/-- /a/. -/
def a : Segment := .ofChart .«a»

/-- /ɘ/, the interior vowel, close-mid and central. -/
def «ɘ» : Segment := .ofChart .«ɘ»

/-- The vowels. -/
def vowels : Finset Segment := ⟨↑[i, u, a, «ɘ»], by decide⟩

/-- The phonemes. -/
def inventory : Finset Segment := consonants ∪ vowels

/-- The vowels are the [+syllabic] phonemes. -/
theorem isVowel_iff : ∀ x ∈ inventory, x.IsVowel ↔ x ∈ vowels := by decide

end Shiwilu
