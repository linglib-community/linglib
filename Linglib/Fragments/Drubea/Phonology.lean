/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Drubea segments

The consonants and vowels of Drubea (Glottocode dumb1241), the southernmost language of
Grande Terre, New Caledonia, as [lionnet-2025] tabulates them after [rivierre-1973] and
[shintani-paita-1990b]. The plosives contrast a voiceless and a prenasalised voiced series,
the latter transcribed as plain voiced stops in the New Caledonian convention the source
follows; labials and velars have labialised partners. The vowels are eight oral and five
nasal qualities, short and long; in the moraic model a long vowel is not a further segment
but two morae on one melody, so the qualities are the segments and length is the weight of
the syllable, `Prosody.Syllable.ofVowel` against `Prosody.Syllable.ofLongVowel`. The lax
front vowel /ɪ/ occurs long only. Syllables are open, (C)V(V). Register is in
`Fragments/Drubea/Prosody`.

The feature values come from the PHOIBLE chart. The chart holds no prenasalised or
labialised segments, whose contours a two-valued matrix cannot express: a prenasalised stop
takes the plain voiced stop's matrix, and a labialised consonant departs from its plain
counterpart by `labialized`, [+round] with [+labial] for the velars. PHOIBLE has no Drubea
inventory. A segment is named by the source's transcription where Lean admits the symbol,
else by the symbol's name.

## Main definitions

* `Drubea.p`, `Drubea.pw`, `Drubea.tRetroflex`, …: the consonants; `Drubea.consonants` the
  set of them.
* `Drubea.i`, `Drubea.smallCapitalI`, `Drubea.iNasal`, …: the vowel qualities;
  `Drubea.vowels`.
* `Drubea.inventory`: the phonemes.

## Main results

* `Drubea.isVowel_iff`: the vowels are the [+syllabic] phonemes.

## References

* [lionnet-2025]
* [rivierre-1973]
* [shintani-paita-1990b]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Drubea

/-! ### Consonants -/

/-- Labialisation: [+round], with [+labial] for a non-labial base. -/
def labialized : Segment := Segment.ofSpecs [(.labial, true), (.round, true)]

/-- /p/. -/
def p : Segment := .ofChart .«p»

/-- /pw/, the labialised bilabial plosive. -/
def pw : Segment := .ofChart .«p» labialized

/-- /t/. -/
def t : Segment := .ofChart .«t»

/-- /ʈ/, the retroflex plosive. -/
def tRetroflex : Segment := .ofChart .«ʈ»

/-- /c/, the palatal plosive. -/
def c : Segment := .ofChart .«c»

/-- /k/. -/
def k : Segment := .ofChart .«k»

/-- /kw/, the labialised velar plosive. -/
def kw : Segment := .ofChart .«k» labialized

/-- /b/, phonetically the prenasalised [ᵐb]. -/
def b : Segment := .ofChart .«b»

/-- /bw/, phonetically [ᵐbʷ]. -/
def bw : Segment := .ofChart .«b» labialized

/-- /d/, phonetically [ⁿd]. -/
def d : Segment := .ofChart .«d»

/-- /ɖ/, phonetically the prenasalised retroflex [ᶯɖ]. -/
def dRetroflex : Segment := .ofChart .«ɖ»

/-- /j/, phonetically the prenasalised palatal [ᶮɟ]; the glide is `y`. -/
def j : Segment := .ofChart .«ɟ»

/-- /g/, phonetically [ᵑɡ]. -/
def g : Segment := .ofChart .«ɡ»

/-- /gw/, phonetically [ᵑɡʷ]; Drubea only, where Numèè has /ŋw/. -/
def gw : Segment := .ofChart .«ɡ» labialized

/-- /m/. -/
def m : Segment := .ofChart .«m»

/-- /mw/. -/
def mw : Segment := .ofChart .«m» labialized

/-- /n/. -/
def n : Segment := .ofChart .«n»

/-- /ɳ/, the retroflex nasal. -/
def nRetroflex : Segment := .ofChart .«ɳ»

/-- /ɲ/, the palatal nasal. -/
def nPalatal : Segment := .ofChart .«ɲ»

/-- /ŋ/. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- /v/. -/
def v : Segment := .ofChart .«v»

/-- /x/, phonetically [ɣ]. -/
def x : Segment := .ofChart .«x»

/-- /ɽ/, the retroflex flap. -/
def rRetroflex : Segment := .ofChart .«ɽ»

/-- /y/, the palatal glide [j]. -/
def y : Segment := .ofChart .«j»

/-- /w/. -/
def w : Segment := .ofChart .«w»

/-- The consonants ((1) of [lionnet-2025]). -/
def consonants : Finset Segment :=
  ⟨↑[p, pw, t, tRetroflex, c, k, kw, b, bw, d, dRetroflex, j, g, gw, m, mw, n, nRetroflex,
      nPalatal, ŋ, v, x, rRetroflex, y, w], by decide⟩

/-! ### Vowels -/

/-- /i/. -/
def i : Segment := .ofChart .«i»

/-- /u/. -/
def u : Segment := .ofChart .«u»

/-- /e/. -/
def e : Segment := .ofChart .«e»

/-- /ɪ/, long only. -/
def smallCapitalI : Segment := .ofChart .«ɪ»

/-- /ʊ/. -/
def upsilon : Segment := .ofChart .«ʊ»

/-- /ɛ/. -/
def openE : Segment := .ofChart .«ɛ»

/-- /o/. -/
def o : Segment := .ofChart .«o»

/-- /a/. -/
def a : Segment := .ofChart .«a»

/-- /ĩ/. -/
def iNasal : Segment := .ofChart .«ĩ»

/-- /ũ/. -/
def uNasal : Segment := .ofChart .«ũ»

/-- /ẽ/. -/
def eNasal : Segment := .ofChart .«ẽ»

/-- /õ/. -/
def oNasal : Segment := .ofChart .«õ»

/-- /ã/. -/
def aNasal : Segment := .ofChart .«ã»

/-- The vowel qualities ((2) of [lionnet-2025]). -/
def vowels : Finset Segment :=
  ⟨↑[i, u, e, smallCapitalI, upsilon, openE, o, a, iNasal, uNasal, eNasal, oNasal, aNasal],
    by decide⟩

/-- The phonemes. -/
def inventory : Finset Segment := consonants ∪ vowels

/-- The vowels are the [+syllabic] phonemes. -/
theorem isVowel_iff : ∀ s ∈ inventory, s.IsVowel ↔ s ∈ vowels := by decide

end Drubea
