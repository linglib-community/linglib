/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Poko segments

The consonants and vowels of Poko (Glottocode rawo1244), a Skou language of Papua New Guinea,
as [mcpherson-dryer-2021] tabulate them. The plosives contrast voicing at the bilabial and
alveolar places, the velar place has /k/ alone, and voiceless /t/ occurs in only four words.
There is a bilabial trill, written ⟨br⟩ in the practical orthography and prenasalised
word-medially. There is no phonemic /ɡ/: the velar nasal /ŋ/ is a prenasalised plosive [ŋɡ]
in an onset and [ŋ] in a coda. The vowels are the five qualities /i e a o u/, which also
form the diphthongs /ia ua ue ui/. Every stem ends in a vowel underlyingly. Tone is in
`Fragments/Poko/Tone`.

## Implementation notes

The feature values come from the PHOIBLE chart, which has no Poko inventory. A diphthong is
not a further segment but the sequence of its two vowels. A segment is named by its IPA symbol
where Lean admits it, else by the symbol's name.

## References

* [mcpherson-dryer-2021]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Poko

/-! ### Consonants -/

/-- /p/. -/
def p : Segment := .ofChart .«p»

/-- /b/. -/
def b : Segment := .ofChart .«b»

/-- /t/, found in only four words. -/
def t : Segment := .ofChart .«t»

/-- /d/. -/
def d : Segment := .ofChart .«d»

/-- /k/. -/
def k : Segment := .ofChart .«k»

/-- /m/. -/
def m : Segment := .ofChart .«m»

/-- /n/. -/
def n : Segment := .ofChart .«n»

/-- /ŋ/, written ⟨ng⟩: the prenasalised plosive [ŋɡ] in an onset, [ŋ] in a coda. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- /s/. -/
def s : Segment := .ofChart .«s»

/-- /ʙ/, the bilabial trill, written ⟨br⟩ and prenasalised word-medially. -/
def smallCapitalB : Segment := .ofChart .«ʙ»

/-- /r/. -/
def r : Segment := .ofChart .«r»

/-- /l/. -/
def l : Segment := .ofChart .«l»

/-- /w/. -/
def w : Segment := .ofChart .«w»

/-- /j/, the palatal glide, written ⟨y⟩. -/
def j : Segment := .ofChart .«j»

/-- The consonants (Table 1 of [mcpherson-dryer-2021]). -/
def consonants : Finset Segment :=
  ⟨↑[p, b, t, d, k, m, n, ŋ, s, smallCapitalB, r, l, w, j], by decide⟩

/-! ### Vowels -/

/-- /i/. -/
def i : Segment := .ofChart .«i»

/-- /e/. -/
def e : Segment := .ofChart .«e»

/-- /a/. -/
def a : Segment := .ofChart .«a»

/-- /o/. -/
def o : Segment := .ofChart .«o»

/-- /u/. -/
def u : Segment := .ofChart .«u»

/-- The vowel qualities. -/
def vowels : Finset Segment := ⟨↑[i, e, a, o, u], by decide⟩

/-- The phonemes. -/
def inventory : Finset Segment := consonants ∪ vowels

/-- The vowels are the [+syllabic] phonemes. -/
theorem isVowel_iff : ∀ s ∈ inventory, s.IsVowel ↔ s ∈ vowels := by decide

end Poko
