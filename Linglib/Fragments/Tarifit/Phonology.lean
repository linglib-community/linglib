module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Tarifit phones

This file gives the consonants of Tarifit (Nador variety) that occur in the triconsonantal verbs
of Afkir and Zellou's production study, as they surface in the simple imperative, together with
the schwa. Tarifit spirantizes: the historical bilabial and dental stops surface as the
fricatives /β ð θ/ except when geminated. A phone is named by its IPA symbol, and its sonority
class is read off its features by `Sonority.Class.ofSegment` and not stored.

The feature values come from the PHOIBLE chart, which has no Tarifit inventory, and a phone is
its chart entry's segment with the phone's departure merged over it. There are two departures.
PHOIBLE gives the pharyngealized stop /tˤ/ a contour tongue-root value, which the chart omits, so
it takes the chart's /t/ with [+RTR], as the chart's /d̙ˤ/ is its /d/ with [+RTR]. The book's
consonant chart lists /ʕ/ among the fricatives, but its text groups /ʕ/ with /r/ as a sonorant
that conditions vowels, and its count of rising, plateauing and falling onsets holds only with
/ʕ/ above the tap, so /ʕ/ is the chart's segment as an approximant.

## References

* [afkir-zellou-2025]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Tarifit

/-! ### Phones -/

/-- The voiceless uvular stop /q/. -/
def q : Segment := .ofChart .«q»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The pharyngealized voiceless stop /tˤ/. -/
def «tˤ» : Segment := .ofChart .«t» (Segment.ofSpecs [(.rtr, true)])

/-- The pharyngealized voiced stop /dˤ/. -/
def «dˤ» : Segment := .ofChart .«d̙ˤ»

/-- The voiced bilabial fricative /β/. -/
def β : Segment := .ofChart .«β»

/-- The voiced dental fricative /ð/. -/
def ð : Segment := .ofChart .«ð»

/-- The voiceless dental fricative /θ/. -/
def θ : Segment := .ofChart .«θ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiceless uvular fricative /χ/. -/
def χ : Segment := .ofChart .«χ»

/-- The voiceless pharyngeal fricative /ħ/. -/
def ħ : Segment := .ofChart .«ħ»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiced postalveolar fricative /ʒ/. -/
def «ʒ» : Segment := .ofChart .«ʒ»

/-- The voiced uvular fricative /ʁ/. -/
def «ʁ» : Segment := .ofChart .«ʁ»

/-- The pharyngeal approximant /ʕ/. -/
def «ʕ» : Segment :=
  .ofChart .«ʕ» (Segment.ofSpecs [(.consonantal, false), (.sonorant, true), (.approximant, true)])

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The alveolar tap /r/. -/
def r : Segment := .ofChart .«ɾ»

/-- The alveolar lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The schwa /ə/. -/
def «ə» : Segment := .ofChart .«ə»

/-- The phones, each with its IPA transcription. -/
def transcriptions : List (Segment × String) :=
  [(q, "q"), (k, "k"), (t, "t"), («tˤ», "tˤ"), («dˤ», "dˤ"), (β, "β"), (ð, "ð"), (θ, "θ"),
    (f, "f"), (s, "s"), («ʃ», "ʃ"), (χ, "χ"), (ħ, "ħ"), (z, "z"), («ʒ», "ʒ"), («ʁ», "ʁ"),
    («ʕ», "ʕ"), (m, "m"), (n, "n"), (r, "r"), (l, "l"), («ə», "ə")]

/-- The phones, pairwise distinct. -/
def inventory : Finset Segment := ⟨↑(transcriptions.map (·.1)), by decide⟩

/-- The IPA transcription of a phone. -/
def ipa? (x : Segment) : Option String := transcriptions.lookup x

end Tarifit
