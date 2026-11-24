module

public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Punjabi phonology

This file defines the segments of Punjabi (Panjabi): the consonants that [bhatia-1993] describes
for standard spoken Punjabi, and the ten oral vowels with the nasal counterparts of the seven
long ones, the inventory of [shackle-2003] as [paramore-bennett-2026] chart it for the Panjabi of
Pakistan.

The phonemes are segments named by their symbols, with feature values from the PHOIBLE chart. A
long vowel is written with its symbol doubled, as is usual for Indo-Aryan languages, so that
`ii` is the long high front vowel and `«ɪ»` its short lax counterpart. Every long vowel
contrasts in nasality, and a nasal vowel is its oral counterpart with [+nasal]. `ofGlyph?`
reads a segment from its symbol.

## Implementation notes

Segments carry no length, so a long vowel and a short one differ in quality alone, and the
distinctive length of consonants is not represented. Tone is not represented. The stops and the
nasal that the grammar calls apico-dental are the chart's dentals, while its apico-dental
fricatives, lateral and trill are the chart's `s`, `z`, `l` and `r`. Its palatal affricates are
the chart's postalveolar ones, its fricative transcribed *sh*, which it calls retroflex, the
chart's `ʃ`, its voiced glottal fricative the chart's `ɦ`, and its labial semivowel the chart's
labiodental approximant. The grammar gives `f`, `z`, `x`, `ɣ` and `q` as sounds of Perso-Arabic
and English words, whose phonemic status it calls questionable; they are `loanConsonants`. Its
chart of segments has a palatal and a velar nasal, which its description gives as realizations
of `n` before palatal and velar stops; they are not phonemes here. On the chart's values the
glottal fricative is [−consonantal], with the vowels and the semivowels.

## References

* [T. K. Bhatia, *Punjabi: A Cognitive-Descriptive Grammar* (1993)][bhatia-1993]
* [C. Shackle, *Panjabi* (2003)][shackle-2003]
* [J. C. Paramore and R. Bennett, *Covert URs: Evidence from nasalization in Panjabi*
  (2026)][paramore-bennett-2026]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Punjabi.Phonology

/-! ### Vowels -/

/-- The long high front vowel `ii`. -/
def ii : Segment := .ofChart .«i»

/-- The short lax high front vowel `ɪ`. -/
def «ɪ» : Segment := .ofChart .«ɪ»

/-- The long mid front tense vowel `ee`. -/
def ee : Segment := .ofChart .«e»

/-- The long mid front lax vowel `ɛɛ`. -/
def «ɛɛ» : Segment := .ofChart .«ɛ»

/-- The short central vowel `ə`. -/
def «ə» : Segment := .ofChart .«ə»

/-- The long low back vowel `ɑɑ`. -/
def «ɑɑ» : Segment := .ofChart .«ɑ»

/-- The long mid back lax vowel `ɔɔ`. -/
def «ɔɔ» : Segment := .ofChart .«ɔ»

/-- The long mid back tense vowel `oo`. -/
def oo : Segment := .ofChart .«o»

/-- The short lax high back vowel `ʊ`. -/
def «ʊ» : Segment := .ofChart .«ʊ»

/-- The long high back vowel `uu`. -/
def uu : Segment := .ofChart .«u»

/-- The nasal long high front vowel `ĩĩ`. -/
def «ĩĩ» : Segment := .ofChart .«ĩ»

/-- The nasal long mid front tense vowel `ẽẽ`. -/
def «ẽẽ» : Segment := .ofChart .«ẽ»

/-- The nasal long mid front lax vowel `ɛ̃ɛ̃`. -/
def «ɛ̃ɛ̃» : Segment := .ofChart .«ɛ̃»

/-- The nasal long low back vowel `ɑ̃ɑ̃`. -/
def «ɑ̃ɑ̃» : Segment := .ofChart .«ɑ̃»

/-- The nasal long mid back lax vowel `ɔ̃ɔ̃`. -/
def «ɔ̃ɔ̃» : Segment := .ofChart .«ɔ̃»

/-- The nasal long mid back tense vowel `õõ`. -/
def «õõ» : Segment := .ofChart .«õ»

/-- The nasal long high back vowel `ũũ`. -/
def «ũũ» : Segment := .ofChart .«ũ»

/-- The long oral vowels, pairwise distinct. -/
def longVowels : Finset Segment := ⟨↑[ii, ee, «ɛɛ», «ɑɑ», «ɔɔ», oo, uu], by decide⟩

/-- The short vowels, pairwise distinct. -/
def shortVowels : Finset Segment := ⟨↑[«ɪ», «ə», «ʊ»], by decide⟩

/-- The nasal vowels, pairwise distinct. -/
def nasalVowels : Finset Segment :=
  ⟨↑[«ĩĩ», «ẽẽ», «ɛ̃ɛ̃», «ɑ̃ɑ̃», «ɔ̃ɔ̃», «õõ», «ũũ»], by decide⟩

/-- The vowels. -/
def vowels : Finset Segment := longVowels ∪ shortVowels ∪ nasalVowels

/-! ### Consonants -/

/-- The voiceless bilabial stop `p`. -/
def p : Segment := .ofChart .«p»

/-- The voiceless aspirated bilabial stop `pʰ`. -/
def «pʰ» : Segment := .ofChart .«pʰ»

/-- The voiced bilabial stop `b`. -/
def b : Segment := .ofChart .«b»

/-- The voiceless dental stop `t`. -/
def t : Segment := .ofChart .«t̪»

/-- The voiceless aspirated dental stop `tʰ`. -/
def «tʰ» : Segment := .ofChart .«t̪ʰ»

/-- The voiced dental stop `d`. -/
def d : Segment := .ofChart .«d̪»

/-- The voiceless retroflex stop `ʈ`. -/
def «ʈ» : Segment := .ofChart .«ʈ»

/-- The voiceless aspirated retroflex stop `ʈʰ`. -/
def «ʈʰ» : Segment := .ofChart .«ʈʰ»

/-- The voiced retroflex stop `ɖ`. -/
def «ɖ» : Segment := .ofChart .«ɖ»

/-- The voiceless palatal affricate `tʃ`. -/
def «tʃ» : Segment := .ofChart .«t̠ʃ»

/-- The voiceless aspirated palatal affricate `tʃʰ`. -/
def «tʃʰ» : Segment := .ofChart .«t̠ʃʰ»

/-- The voiced palatal affricate `dʒ`. -/
def «dʒ» : Segment := .ofChart .«d̠ʒ»

/-- The voiceless velar stop `k`. -/
def k : Segment := .ofChart .«k»

/-- The voiceless aspirated velar stop `kʰ`. -/
def «kʰ» : Segment := .ofChart .«kʰ»

/-- The voiced velar stop `g`. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless dental fricative `s`. -/
def s : Segment := .ofChart .«s»

/-- The voiceless fricative `ʃ`. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The glottal fricative `h`, /ɦ/. -/
def h : Segment := .ofChart .«ɦ»

/-- The bilabial nasal `m`. -/
def m : Segment := .ofChart .«m»

/-- The dental nasal `n`. -/
def n : Segment := .ofChart .«n̪»

/-- The retroflex nasal `ɳ`. -/
def «ɳ» : Segment := .ofChart .«ɳ»

/-- The dental lateral `l`. -/
def l : Segment := .ofChart .«l»

/-- The retroflex lateral `ɭ`. -/
def «ɭ» : Segment := .ofChart .«ɭ»

/-- The dental trill `r`. -/
def r : Segment := .ofChart .«r»

/-- The retroflex flap `ɽ`. -/
def «ɽ» : Segment := .ofChart .«ɽ»

/-- The labial semivowel `ʋ`. -/
def «ʋ» : Segment := .ofChart .«ʋ»

/-- The palatal semivowel `j`. -/
def j : Segment := .ofChart .«j»

/-- The voiceless labial fricative `f` of loanwords. -/
def f : Segment := .ofChart .«f»

/-- The voiced dental fricative `z` of loanwords. -/
def z : Segment := .ofChart .«z»

/-- The voiceless velar fricative `x` of loanwords. -/
def x : Segment := .ofChart .«x»

/-- The voiced velar fricative `ɣ` of loanwords. -/
def «ɣ» : Segment := .ofChart .«ɣ»

/-- The uvular stop `q` of loanwords. -/
def q : Segment := .ofChart .«q»

/-- The consonants of the native vocabulary, pairwise distinct. -/
def consonants : Finset Segment :=
  ⟨↑[p, «pʰ», b, t, «tʰ», d, «ʈ», «ʈʰ», «ɖ», «tʃ», «tʃʰ», «dʒ», k, «kʰ», g, s, «ʃ», h, m, n,
    «ɳ», l, «ɭ», r, «ɽ», «ʋ», j], by decide⟩

/-- The consonants of Perso-Arabic and English words, pairwise distinct. -/
def loanConsonants : Finset Segment := ⟨↑[f, z, x, «ɣ», q], by decide⟩

/-- The phonemes, the vowels with the native and the borrowed consonants. -/
def phonemes : Finset Segment := vowels ∪ consonants ∪ loanConsonants

/-! ### Classes -/

/-- The nasal counterpart of each long vowel is the vowel with [+nasal]. -/
theorem nasal_eq :
    ii.setFeature .nasal true = «ĩĩ» ∧ ee.setFeature .nasal true = «ẽẽ» ∧
      «ɛɛ».setFeature .nasal true = «ɛ̃ɛ̃» ∧ «ɑɑ».setFeature .nasal true = «ɑ̃ɑ̃» ∧
      «ɔɔ».setFeature .nasal true = «ɔ̃ɔ̃» ∧ oo.setFeature .nasal true = «õõ» ∧
      uu.setFeature .nasal true = «ũũ» := by
  decide

/-- The syllabic phonemes are the vowels. -/
theorem isSyllabic_iff_mem_vowels : ∀ x ∈ phonemes, x.IsSyllabic ↔ x ∈ vowels := by
  decide +kernel

/-- No vowel is consonantal. -/
theorem isVowel_of_mem_vowels : ∀ x ∈ vowels, x.IsVowel := by decide +kernel

/-- The nonsyllabic phonemes that are not consonantal are the two semivowels and the glottal
fricative. -/
theorem naturalClass_nonsyllabic_nonconsonantal :
    naturalClass [−syllabic, −consonantal] phonemes = {«ʋ», j, h} := by
  decide +kernel

/-- The nasal consonants are the consonantal nasal phonemes. -/
theorem naturalClass_nasal_consonantal :
    naturalClass [+consonantal, +nasal] phonemes = {m, n, «ɳ»} := by
  decide +kernel

/-- The nasal phonemes that are not consonantal are the nasal vowels, so no semivowel is
nasal. -/
theorem naturalClass_nasal_vocoid :
    naturalClass [−consonantal, +nasal] phonemes = nasalVowels := by
  decide +kernel

/-! ### Spelling -/

/-- `ofGlyph? g` is the phoneme that the symbol `g` writes. -/
def ofGlyph? : String → Option Segment
  | "ii" => some ii | "ɪ" => some «ɪ» | "ee" => some ee | "ɛɛ" => some «ɛɛ» | "ə" => some «ə»
  | "ɑɑ" => some «ɑɑ» | "ɔɔ" => some «ɔɔ» | "oo" => some oo | "ʊ" => some «ʊ» | "uu" => some uu
  | "ĩĩ" => some «ĩĩ» | "ẽẽ" => some «ẽẽ» | "ɛ̃ɛ̃" => some «ɛ̃ɛ̃» | "ɑ̃ɑ̃" => some «ɑ̃ɑ̃»
  | "ɔ̃ɔ̃" => some «ɔ̃ɔ̃» | "õõ" => some «õõ» | "ũũ" => some «ũũ»
  | "p" => some p | "pʰ" => some «pʰ» | "b" => some b | "t" => some t | "tʰ" => some «tʰ»
  | "d" => some d | "ʈ" => some «ʈ» | "ʈʰ" => some «ʈʰ» | "ɖ" => some «ɖ» | "tʃ" => some «tʃ»
  | "tʃʰ" => some «tʃʰ» | "dʒ" => some «dʒ» | "k" => some k | "kʰ" => some «kʰ» | "g" => some g
  | "s" => some s | "ʃ" => some «ʃ» | "h" => some h | "m" => some m | "n" => some n
  | "ɳ" => some «ɳ» | "l" => some l | "ɭ" => some «ɭ» | "r" => some r | "ɽ" => some «ɽ»
  | "ʋ" => some «ʋ» | "j" => some j | "f" => some f | "z" => some z | "x" => some x
  | "ɣ" => some «ɣ» | "q" => some q
  | _ => none

end Punjabi.Phonology
