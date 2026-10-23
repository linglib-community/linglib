module

public import Linglib.Data.PHOIBLE.Inventories.IsraeliHebrew
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Segmental.NaturalClass

/-!
# Modern Hebrew phonology

This file defines the 20 consonants and five vowels of Modern Hebrew, as in PHOIBLE's
inventory 2449 of Israeli Hebrew, as segments named by their IPA symbols, with feature values
from the PHOIBLE chart.

The stops /b/, /k/ and /p/ alternate with the fricatives /v/, /x/ and /f/ in native words, but
only where the root consonant is the historical ב, כ or פ; the /k/ of ק and the /v/ of ו never
alternate. The alternating consonant of a root is the archisegment `B`, `K` or `P`, the meet of
its two alternants, which leaves continuancy and the features that go with it unspecified; a
spirantization rule fills them in.

## Main definitions

* `b`, `d`, …, `ʔ`: the consonants, and `consonants`, the set of them.
* `a`, `ɛ`, `i`, `o`, `u`: the vowels, and `vowels`, the set of them.
* `B`, `K`, `P`: the archisegments of the alternating stops.

## Main results

* `heb_phonemes_map`: the consonants and vowels are the segments of inventory 2449's phonemes.
* `unspecified_continuant`: the archisegments, and only they, leave continuancy unspecified.
* `naturalClass_setFeature_continuant`: each archisegment has one stop and one fricative.

## References

* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Hebrew.Phonology

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiced velar stop /ɡ/. -/
def «ɡ» : Segment := .ofChart .«ɡ»

/-- The voiceless glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The alveolar lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiced uvular fricative /ʁ/, the Modern Hebrew r. -/
def «ʁ» : Segment := .ofChart .«ʁ»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiceless alveolar affricate /ts/. -/
def ts : Segment := .ofChart .«ts»

/-- The voiced labiodental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The voiceless velar fricative /x/. -/
def x : Segment := .ofChart .«x»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The glottal stop /ʔ/. -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- The consonants of Modern Hebrew. -/
def consonants : Finset Segment :=
  ⟨↑[b, d, f, «ɡ», h, j, k, l, m, n, p, «ʁ», s, «ʃ», t, ts, v, x, z, «ʔ»], by decide +kernel⟩

/-- The open vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The open-mid front vowel /ɛ/. -/
def «ɛ» : Segment := .ofChart .«ɛ»

/-- The close front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close-mid back vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The close back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The vowels of Modern Hebrew. -/
def vowels : Finset Segment := ⟨↑[a, «ɛ», i, o, u], by decide +kernel⟩

/-- The consonants and vowels, in the order of PHOIBLE's inventory 2449, are the segments of its
phonemes. -/
theorem heb_phonemes_map :
    Inventories.IsraeliHebrew.heb.phonemes.map (Segment.ofChart ·.features) =
      [b, d, f, h, j, k, l, m, n, p, s, t, ts, v, x, z, «ɡ», «ʁ», «ʃ», «ʔ», a, i, o, u, «ɛ»] :=
  rfl

/-! ### The alternating stops -/

/-- The archisegment of the alternating ב, the meet of /b/ and /v/. -/
def B : Segment := b ⊓ v

/-- The archisegment of the alternating כ, the meet of /k/ and /x/. -/
def K : Segment := k ⊓ x

/-- The archisegment of the alternating פ, the meet of /p/ and /f/. -/
def P : Segment := p ⊓ f

/-- The archisegments leave continuancy unspecified, and every consonant and vowel specifies
it. -/
theorem unspecified_continuant :
    (∀ x ∈ [B, K, P], x.Unspecified .continuant) ∧
      ∀ x ∈ consonants ∪ vowels, ¬x.Unspecified .continuant := by
  decide +kernel

/-- Each archisegment has one stop and one fricative among the consonants, since with continuancy
set `B`, `K` and `P` pick out /b/ and /v/, /k/ and /x/, /p/ and /f/. -/
theorem naturalClass_setFeature_continuant :
    (B.setFeature .continuant false).naturalClass consonants = {b} ∧
      (B.setFeature .continuant true).naturalClass consonants = {v} ∧
      (K.setFeature .continuant false).naturalClass consonants = {k} ∧
      (K.setFeature .continuant true).naturalClass consonants = {x} ∧
      (P.setFeature .continuant false).naturalClass consonants = {p} ∧
      (P.setFeature .continuant true).naturalClass consonants = {f} := by
  decide +kernel

end Hebrew.Phonology
