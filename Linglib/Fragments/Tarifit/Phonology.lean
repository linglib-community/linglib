module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Tarifit phonology

This file defines the phonemes of Tarifit (Nador variety) as Afkir and Zellou chart them: the
consonants of their Figure 6, the four vowels /a i u ə/, and the marginal /l/ and /p/ of recent
loans. A phoneme is named by its IPA symbol, with feature values from the PHOIBLE chart, which has
no Tarifit inventory. The coronal stops are dental, as the text calls them. Length is not a
feature here: a geminate is a consonant on two timing slots, and `geminates` collects the
consonants that the chart lists geminated.

The chart has no entry for the pharyngealized and labialized consonants, whose tongue-root and
labial values PHOIBLE gives as contours, so each is the plain consonant with [+RTR] or with
[+round] and [−labiodental]. The chart lists /ʕ/ among the fricatives, but the text groups it
with /r/ as a sonorant that conditions vowels, and the count of rising, plateauing and falling
onsets holds only with /ʕ/ above the tap, so /ʕ/ is the chart's segment as an approximant.

## Main definitions

* `Tarifit.consonants`, `Tarifit.geminates`: the consonants of Figure 6, singly and geminated.
* `Tarifit.vowels`, `Tarifit.marginal`: the vowels, and the consonants of recent loans.
* `Tarifit.ipa?`: the IPA transcription of a phoneme.

## References

* [afkir-zellou-2025]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Tarifit

/-- The departure of a pharyngealized consonant from the plain one. -/
def pharyngealization : Segment := .ofSpecs [(.rtr, true)]

/-- The departure of a labialized consonant from the plain one. -/
def labialization : Segment := .ofSpecs [(.round, true), (.labiodental, false)]

/-! ### Stops -/

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiceless dental stop /t/. -/
def t : Segment := .ofChart .«t̪»

/-- The voiced dental stop /d/. -/
def d : Segment := .ofChart .«d̪»

/-- The pharyngealized voiceless dental stop /tˤ/. -/
def «tˤ» : Segment := .ofChart .«t̪» pharyngealization

/-- The pharyngealized voiced dental stop /dˤ/. -/
def «dˤ» : Segment := .ofChart .«d̪» pharyngealization

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar stop /g/. -/
def g : Segment := .ofChart .«ɡ»

/-- The pharyngealized voiced velar stop /gˤ/. -/
def «gˤ» : Segment := .ofChart .«ɡ» pharyngealization

/-- The labialized voiceless velar stop /kʷ/. -/
def «kʷ» : Segment := .ofChart .«k» labialization

/-- The labialized voiced velar stop /gʷ/. -/
def «gʷ» : Segment := .ofChart .«ɡ» labialization

/-- The voiceless uvular stop /q/. -/
def q : Segment := .ofChart .«q»

/-! ### Sonorants -/

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The pharyngealized bilabial nasal /mˤ/. -/
def «mˤ» : Segment := .ofChart .«m» pharyngealization

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The labialized alveolar nasal /nʷ/. -/
def «nʷ» : Segment := .ofChart .«n» labialization

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The labialized palatal glide /jʷ/. -/
def «jʷ» : Segment := .ofChart .«j» labialization

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-! ### Fricatives -/

/-- The voiced bilabial fricative /β/. -/
def β : Segment := .ofChart .«β»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiceless dental fricative /θ/. -/
def θ : Segment := .ofChart .«θ»

/-- The voiced dental fricative /ð/. -/
def ð : Segment := .ofChart .«ð»

/-- The pharyngealized voiced dental fricative /ðˤ/. -/
def «ðˤ» : Segment := .ofChart .«ð» pharyngealization

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The pharyngealized voiceless alveolar fricative /sˤ/. -/
def «sˤ» : Segment := .ofChart .«s» pharyngealization

/-- The pharyngealized voiced alveolar fricative /zˤ/. -/
def «zˤ» : Segment := .ofChart .«z» pharyngealization

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar fricative /ʒ/. -/
def «ʒ» : Segment := .ofChart .«ʒ»

/-- The pharyngealized voiced postalveolar fricative /ʒˤ/. -/
def «ʒˤ» : Segment := .ofChart .«ʒ» pharyngealization

/-- The pharyngealized labialized voiceless postalveolar fricative /ʃˤʷ/, which the chart lists
only geminated. -/
def «ʃˤʷ» : Segment :=
  .ofChart .«ʃ» (.ofSpecs [(.rtr, true), (.round, true), (.labiodental, false)])

/-- The voiceless uvular fricative /χ/. -/
def χ : Segment := .ofChart .«χ»

/-- The pharyngealized voiceless uvular fricative /χˤ/. -/
def «χˤ» : Segment := .ofChart .«χ» pharyngealization

/-- The voiced uvular fricative /ʁ/. -/
def «ʁ» : Segment := .ofChart .«ʁ»

/-- The pharyngealized voiced uvular fricative /ʁˤ/. -/
def «ʁˤ» : Segment := .ofChart .«ʁ» pharyngealization

/-- The voiceless pharyngeal fricative /ħ/. -/
def ħ : Segment := .ofChart .«ħ»

/-- The pharyngeal approximant /ʕ/. -/
def «ʕ» : Segment :=
  .ofChart .«ʕ» (.ofSpecs [(.consonantal, false), (.sonorant, true), (.approximant, true)])

/-- The voiceless glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-! ### Affricates and taps -/

/-- The voiceless postalveolar affricate /tʃ/. -/
def «tʃ» : Segment := .ofChart .«t̠ʃ»

/-- The voiced postalveolar affricate /dʒ/. -/
def «dʒ» : Segment := .ofChart .«d̠ʒ»

/-- The alveolar tap /r/. -/
def r : Segment := .ofChart .«ɾ»

/-- The pharyngealized alveolar tap /rˤ/. -/
def «rˤ» : Segment := .ofChart .«ɾ» pharyngealization

/-! ### Vowels and loan consonants -/

/-- The open vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The close front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The schwa /ə/. -/
def «ə» : Segment := .ofChart .«ə»

/-- The alveolar lateral /l/, which merged with /r/ and returned in recent loans. -/
def l : Segment := .ofChart .«l»

/-- The voiceless bilabial stop /p/ of loans from Spanish and French. -/
def p : Segment := .ofChart .«p»

/-! ### The inventory -/

/-- The consonants of Figure 6, singly. -/
def consonants : Finset Segment :=
  ⟨↑[b, t, d, «tˤ», «dˤ», k, g, «gˤ», «kʷ», «gʷ», q, m, «mˤ», n, «nʷ», j, «jʷ», w, β, f, θ, ð,
    «ðˤ», s, z, «sˤ», «zˤ», «ʃ», «ʒ», «ʒˤ», χ, «χˤ», «ʁ», «ʁˤ», ħ, «ʕ», h, «tʃ», «dʒ», r, «rˤ»],
    by decide +kernel⟩

/-- The consonants that Figure 6 lists geminated, each a consonant on two timing slots. -/
def geminates : Finset Segment :=
  ⟨↑[b, t, d, «tˤ», «dˤ», k, g, «kʷ», «gʷ», q, m, «mˤ», n, «nʷ», j, w, f, s, z, «sˤ», «zˤ», «ʃ»,
    «ʃˤʷ», «ʒ», «ʒˤ», χ, «χˤ», «ʁ», ħ, «ʕ», h, «dʒ», r, «rˤ»], by decide +kernel⟩

/-- The vowels: the full vowels /a i u/ and the schwa. -/
def vowels : Finset Segment := ⟨↑[a, i, u, «ə»], by decide +kernel⟩

/-- The consonants of recent loans outside Figure 6. -/
def marginal : Finset Segment := ⟨↑[l, p], by decide +kernel⟩

/-- The phonemes, each with its IPA transcription. -/
def transcriptions : List (Segment × String) :=
  [(b, "b"), (t, "t"), (d, "d"), («tˤ», "tˤ"), («dˤ», "dˤ"), (k, "k"), (g, "g"), («gˤ», "gˤ"),
    («kʷ», "kʷ"), («gʷ», "gʷ"), (q, "q"), (m, "m"), («mˤ», "mˤ"), (n, "n"), («nʷ», "nʷ"),
    (j, "j"), («jʷ», "jʷ"), (w, "w"), (β, "β"), (f, "f"), (θ, "θ"), (ð, "ð"), («ðˤ», "ðˤ"),
    (s, "s"), (z, "z"), («sˤ», "sˤ"), («zˤ», "zˤ"), («ʃ», "ʃ"), («ʒ», "ʒ"), («ʒˤ», "ʒˤ"),
    («ʃˤʷ», "ʃˤʷ"), (χ, "χ"), («χˤ», "χˤ"), («ʁ», "ʁ"), («ʁˤ», "ʁˤ"), (ħ, "ħ"), («ʕ», "ʕ"),
    (h, "h"), («tʃ», "tʃ"), («dʒ», "dʒ"), (r, "r"), («rˤ», "rˤ"), (a, "a"), (i, "i"), (u, "u"),
    («ə», "ə"), (l, "l"), (p, "p")]

/-- The IPA transcription of a phoneme. -/
def ipa? (x : Segment) : Option String := transcriptions.lookup x

end Tarifit
