/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.PHOIBLE.Inventories.Tigre
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Morphology.Root.Consonantal

/-!
# Tigre phonology

This file defines the 26 consonants and seven vowels of Tigre, as in PHOIBLE's inventory 576,
as segments named by their IPA symbols, with feature values from the PHOIBLE chart, and the
verbal roots of [faust-lampitelli-2026]'s Tigre paradigms as roots of those segments. The
inventory's coronal stops and nasal are dental. The vowels are the six full qualities and the
weak [ɨ] that Faust and Lampitelli give Tigre as they give Tigrinya: inventory 576 instead lists
the full vowels as long and gives its two central vowels, ə and ɜ, the same feature values.
Faust and Lampitelli write the ejectives with a superscript ʔ or ʕ;
their kˀ is /kʼ/, their tˀ and tˁ are /tʼ/, and their sˁ is /tsʼ/, the inventory's one
ejective sibilant.

## Main definitions

* `b`, `d̠ʒ`, …, `ʕ`: the consonants, and `consonants`, the set of them.
* `a`, `ʌ`, …, `ɨ`: the vowels, and `vowels`, the set of them.

## Main results

* `tig_phonemes_map`: the consonants are the segments of inventory 576's consonants.

## References

* [moran-mccloy-2019]
* [raz-1983]
* [lowenstamm-prunet-1988]
* [faust-lampitelli-2026]
-/

@[expose] public section

open Morphology Phonology Data.PHOIBLE

namespace Tigre.Phonology

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiced postalveolar affricate /d̠ʒ/. -/
def «d̠ʒ» : Segment := .ofChart .«d̠ʒ»

/-- The voiced dental stop /d/. -/
def d : Segment := .ofChart .«d̪»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiceless glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The velar ejective /kʼ/. -/
def «kʼ» : Segment := .ofChart .«kʼ»

/-- The alveolar lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The dental nasal /n/. -/
def n : Segment := .ofChart .«n̪»

/-- The alveolar trill /r/. -/
def r : Segment := .ofChart .«r»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The alveolar ejective affricate /tsʼ/. -/
def «tsʼ» : Segment := .ofChart .«tsʼ»

/-- The voiceless postalveolar affricate /t̠ʃ/. -/
def «t̠ʃ» : Segment := .ofChart .«t̠ʃ»

/-- The postalveolar ejective affricate /t̠ʃʼ/. -/
def «t̠ʃʼ» : Segment := .ofChart .«t̠ʃʼ»

/-- The voiceless dental stop /t/. -/
def t : Segment := .ofChart .«t̪»

/-- The dental ejective /tʼ/. -/
def «tʼ» : Segment := .ofChart .«t̪ʼ»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless pharyngeal fricative /ħ/. -/
def ħ : Segment := .ofChart .«ħ»

/-- The voiced velar stop /ɡ/. -/
def «ɡ» : Segment := .ofChart .«ɡ»

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar fricative /ʒ/. -/
def «ʒ» : Segment := .ofChart .«ʒ»

/-- The glottal stop /ʔ/. -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- The voiced pharyngeal fricative /ʕ/. -/
def «ʕ» : Segment := .ofChart .«ʕ»

/-- The consonants of Tigre. -/
def consonants : Finset Segment :=
  ⟨↑[b, «d̠ʒ», d, f, h, j, k, «kʼ», l, m, n, r, s, «tsʼ», «t̠ʃ», «t̠ʃʼ», t, «tʼ», w, z, ħ, «ɡ»,
    «ʃ», «ʒ», «ʔ», «ʕ»], by decide +kernel⟩

/-- The open front vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The open-mid back unrounded vowel /ʌ/. -/
def «ʌ» : Segment := .ofChart .«ʌ»

/-- The close front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The close-mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The close-mid back vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The close central vowel, the weak vowel /ɨ/. -/
def «ɨ» : Segment := .ofChart .«ɨ»

/-- The vowels of Tigre. -/
def vowels : Finset Segment := ⟨↑[a, «ʌ», i, u, e, o, «ɨ»], by decide +kernel⟩

/-- The consonants, in the order of PHOIBLE's inventory 576, are the segments of its
nonsyllabic phonemes. -/
theorem tig_phonemes_map :
    (Inventories.Tigre.tig.phonemes.filter (·.features .syllabic = some false)).map
        (Segment.ofChart ·.features) =
      [b, «d̠ʒ», d, f, h, j, k, «kʼ», l, m, n, r, s, «tsʼ», «t̠ʃ», «t̠ʃʼ», t, «tʼ», w, z, ħ, «ɡ»,
        «ʃ», «ʒ», «ʔ», «ʕ»] :=
  rfl

/-! ### Verbal roots -/

/-- √mzn 'weigh' gives [tɨ-mazzɨn] 2-JUSS and [mazzɨn] IMP. -/
def weigh : ConsonantalRoot Segment := ⟨[m, z, n]⟩

/-- √fgr 'leave' gives [fagr-a] PRF-3MSG, [tɨ-fgʌr] 2-JUSS and [fɨgʌr] IMP. -/
def leave : ConsonantalRoot Segment := ⟨[f, «ɡ», r]⟩

/-- √ħtˁb 'wash' gives [ħatˁb-a] PRF-3MSG and [tɨ-ħɨtˁʌb] 2-JUSS. -/
def wash : ConsonantalRoot Segment := ⟨[ħ, «tʼ», b]⟩

/-- √hrb 'flee' gives [harb-a] PRF-3MSG; the 2-JUSS is printed [tɨ-ħɨrʌb]. -/
def flee : ConsonantalRoot Segment := ⟨[h, r, b]⟩

/-- √kˀnsˁ 'get up' gives [tɨ-kˀnʌsˁ] 2-JUSS and [kˀɨnʌsˁ] IMP. -/
def getUp : ConsonantalRoot Segment := ⟨[«kʼ», n, «tsʼ»]⟩

/-- √fgr 'whip' gives [tɨ-fʌggɨr] 2-IMP.M. -/
def whip : ConsonantalRoot Segment := ⟨[f, «ɡ», r]⟩

/-- √sʔl 'ask' gives [tɨ-sʔɨl] 2-IMP.M. -/
def ask : ConsonantalRoot Segment := ⟨[s, «ʔ», l]⟩

/-- √tˀʕn 'load' gives [tɨ-tˀʕɨn] 2-IMP.M. -/
def load : ConsonantalRoot Segment := ⟨[«tʼ», «ʕ», n]⟩

/-- √sħk 'uncover' gives [tɨ-sħɨk] 2-IMP.M. -/
def uncover : ConsonantalRoot Segment := ⟨[s, ħ, k]⟩

/-- √sħb 'pull' gives [tɨ-sħɨb] 2-IMP.M. -/
def pull : ConsonantalRoot Segment := ⟨[s, ħ, b]⟩

end Tigre.Phonology
