module

public import Linglib.Data.PHOIBLE.Inventories.Amharic
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Amharic phonology

This file defines the 31 consonants and seven vowels of Amharic, as in PHOIBLE's inventory 131,
as segments named by their IPA symbols, with feature values from the PHOIBLE chart. The
inventory also lists the geminates, which are not further phonemes here. The chart has no entry
for the labialized consonants, whose [labial] value PHOIBLE gives as a contour, so each is the
plain consonant with [+round], [−labiodental] and no [labial] value, as the inventory gives it.

## Main definitions

* `b`, `d`, …, `ʔ`: the consonants, and `consonants`, the set of them.
* `a`, `e`, …, `ɨ`: the vowels, and `vowels`, the set of them.

## Main results

* `amh_phonemes_map`: the consonants and vowels are the segments of inventory 131's phonemes
  other than the geminates.

## References

* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Amharic.Phonology

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiced postalveolar affricate /d̠ʒ/. -/
def «d̠ʒ» : Segment := .ofChart .«d̠ʒ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiceless glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The labialized voiceless glottal fricative /hʷ/. -/
def «hʷ» : Segment := .ofChart .«h» (.ofSpecs [(.round, true), (.labiodental, false)])
    (Finset.univ.erase .labial)

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The labialized voiceless velar stop /kʷ/. -/
def «kʷ» : Segment := .ofChart .«k» (.ofSpecs [(.round, true), (.labiodental, false)])
    (Finset.univ.erase .labial)

/-- The labialized velar ejective /kʷʼ/. -/
def «kʷʼ» : Segment := .ofChart .«kʼ» (.ofSpecs [(.round, true), (.labiodental, false)])
    (Finset.univ.erase .labial)

/-- The velar ejective /kʼ/. -/
def «kʼ» : Segment := .ofChart .«kʼ»

/-- The alveolar lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The bilabial ejective /pʼ/. -/
def «pʼ» : Segment := .ofChart .«pʼ»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The alveolar ejective fricative /sʼ/. -/
def «sʼ» : Segment := .ofChart .«sʼ»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The alveolar ejective /tʼ/. -/
def «tʼ» : Segment := .ofChart .«tʼ»

/-- The voiceless postalveolar affricate /t̠ʃ/. -/
def «t̠ʃ» : Segment := .ofChart .«t̠ʃ»

/-- The postalveolar ejective affricate /t̠ʃʼ/. -/
def «t̠ʃʼ» : Segment := .ofChart .«t̠ʃʼ»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiced velar stop /ɡ/. -/
def «ɡ» : Segment := .ofChart .«ɡ»

/-- The labialized voiced velar stop /ɡʷ/. -/
def «ɡʷ» : Segment := .ofChart .«ɡ» (.ofSpecs [(.round, true), (.labiodental, false)])
    (Finset.univ.erase .labial)

/-- The palatal nasal /ɲ/. -/
def «ɲ» : Segment := .ofChart .«ɲ»

/-- The alveolar tap, the Amharic r /ɾ/. -/
def «ɾ» : Segment := .ofChart .«ɾ»

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar fricative /ʒ/. -/
def «ʒ» : Segment := .ofChart .«ʒ»

/-- The glottal stop /ʔ/. -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- The consonants of Amharic. -/
def consonants : Finset Segment :=
  ⟨↑[b, d, «d̠ʒ», f, h, «hʷ», j, k, «kʷ», «kʷʼ», «kʼ», l, m, n, p, «pʼ», s, «sʼ», t, «tʼ», «t̠ʃ»,
    «t̠ʃʼ», w, z, «ɡ», «ɡʷ», «ɲ», «ɾ», «ʃ», «ʒ», «ʔ»], by decide +kernel⟩

/-- The open central vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The close-mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The close front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close-mid back vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The close back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The mid central vowel, the transcription's ä /ə/. -/
def «ə» : Segment := .ofChart .«ə»

/-- The close central vowel /ɨ/. -/
def «ɨ» : Segment := .ofChart .«ɨ»

/-- The vowels of Amharic. -/
def vowels : Finset Segment := ⟨↑[a, e, i, o, u, «ə», «ɨ»], by decide +kernel⟩

/-- The consonants and vowels, in the order of PHOIBLE's inventory 131, are the segments of its
phonemes other than the geminates, which are [+long]. -/
theorem amh_phonemes_map :
    ((Inventories.Amharic.amh.phonemes.filter (·.features .long ≠ some true)).map
        (Segment.ofChart ·.features)) =
    [b, d, «d̠ʒ», f, h, «hʷ», j, k, «kʷ», «kʷʼ», «kʼ», l, m, n, p, «pʼ», s, «sʼ», t, «tʼ», «t̠ʃ»,
      «t̠ʃʼ», w, z, «ɡ», «ɡʷ», «ɲ», «ɾ», «ʃ», «ʒ», «ʔ», a, e, i, o, u, «ə», «ɨ»] := by
  decide +kernel

end Amharic.Phonology
