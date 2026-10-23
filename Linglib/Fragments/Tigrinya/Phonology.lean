/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.PHOIBLE.Inventories.Tigrinya
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Morphology.Root.Consonantal

/-!
# Tigrinya phonology

This file defines the 32 consonants and seven vowels of Tigrinya, as in PHOIBLE's inventory
1350, as segments named by their IPA symbols, with feature values from the PHOIBLE chart, and
the verbal roots of [faust-lampitelli-2026]'s paradigms as roots of those segments. The
inventory also lists the geminates, which are not further phonemes here. The vowels are six
full qualities and the weak [ɨ], which occurs only where its absence would leave an impossible
cluster.

## Main definitions

* `b`, `cʼ`, …, `ʕ`: the consonants, and `consonants`, the set of them.
* `a`, `e`, …, `ʌ`: the vowels, and `vowels`, the set of them.

## Main results

* `tir_phonemes_map`: the consonants and vowels are the segments of inventory 1350's phonemes
  other than the geminates.

## References

* [moran-mccloy-2019]
* [leslau-1941]
* [berhane-1991]
* [denais-1990]
* [buckley-1994]
* [faust-lampitelli-2026]
-/

@[expose] public section

open Morphology Phonology Data.PHOIBLE

namespace Tigrinya.Phonology

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The palatal ejective /cʼ/. -/
def «cʼ» : Segment := .ofChart .«cʼ»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiced postalveolar affricate /d̠ʒ/. -/
def «d̠ʒ» : Segment := .ofChart .«d̠ʒ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

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

/-- The bilabial ejective /pʼ/. -/
def «pʼ» : Segment := .ofChart .«pʼ»

/-- The voiceless uvular stop /q/. -/
def q : Segment := .ofChart .«q»

/-- The uvular ejective /qʼ/. -/
def «qʼ» : Segment := .ofChart .«qʼ»

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

/-- The voiced labiodental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The voiceless velar fricative /x/. -/
def x : Segment := .ofChart .«x»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless pharyngeal fricative /ħ/. -/
def ħ : Segment := .ofChart .«ħ»

/-- The voiced velar stop /ɡ/. -/
def «ɡ» : Segment := .ofChart .«ɡ»

/-- The palatal nasal /ɲ/. -/
def «ɲ» : Segment := .ofChart .«ɲ»

/-- The alveolar tap /ɾ/. -/
def «ɾ» : Segment := .ofChart .«ɾ»

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar fricative /ʒ/. -/
def «ʒ» : Segment := .ofChart .«ʒ»

/-- The glottal stop /ʔ/. -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- The voiced pharyngeal fricative /ʕ/. -/
def «ʕ» : Segment := .ofChart .«ʕ»

/-- The consonants of Tigrinya. -/
def consonants : Finset Segment :=
  ⟨↑[b, «cʼ», d, «d̠ʒ», f, h, j, k, l, m, n, p, «pʼ», q, «qʼ», s, «sʼ», t, «tʼ», «t̠ʃ», v, w, x,
    z, ħ, «ɡ», «ɲ», «ɾ», «ʃ», «ʒ», «ʔ», «ʕ»], by decide +kernel⟩

/-- The open front vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The close-mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The close front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close-mid back vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The close back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The close central vowel, the weak vowel /ɨ/. -/
def «ɨ» : Segment := .ofChart .«ɨ»

/-- The open-mid back unrounded vowel /ʌ/. -/
def «ʌ» : Segment := .ofChart .«ʌ»

/-- The vowels of Tigrinya. -/
def vowels : Finset Segment := ⟨↑[a, e, i, o, u, «ɨ», «ʌ»], by decide +kernel⟩

/-- The consonants and vowels, in the order of PHOIBLE's inventory 1350, are the segments of its
phonemes other than the geminates, which are [+long]. -/
theorem tir_phonemes_map :
    (Inventories.Tigrinya.tir.phonemes.filter (·.features .long ≠ some true)).map
        (Segment.ofChart ·.features) =
      [b, «cʼ», d, «d̠ʒ», f, h, j, k, l, m, n, p, «pʼ», q, «qʼ», s, «sʼ», t, «tʼ», «t̠ʃ», v, w,
        x, z, ħ, «ɡ», «ɲ», «ɾ», «ʃ», «ʒ», «ʔ», «ʕ», a, e, i, o, u, «ɨ», «ʌ»] :=
  rfl

/-! ### Verbal roots -/

/-- √grf 'whip' gives [gʌrʌf-] DEP.PRF, [gʌrif-] PRF, [-gʌrrɨf] IMPRF. -/
def whip : ConsonantalRoot Segment := ⟨[«ɡ», «ɾ», f]⟩

/-- √smʕ 'hear' gives [sʌmaʕ-] DEP.PRF, [sʌmiʕ-] PRF, [-sʌmmɨʕ] IMPRF, [sɨmaʕ] IMP.M. -/
def hear : ConsonantalRoot Segment := ⟨[s, m, «ʕ»]⟩

/-- √ʔsr 'arrest' gives [ʔasʌr-] DEP.PRF, [ʔasir-] PRF, [-ʔassɨr] IMPRF. -/
def arrest : ConsonantalRoot Segment := ⟨[«ʔ», s, «ɾ»]⟩

/-- √sħb 'pull' gives [saħab-] DEP.PRF, [siħib-] PRF, [-sɨħɨb] IMPRF. -/
def pull : ConsonantalRoot Segment := ⟨[s, ħ, b]⟩

/-- √mhr 'teach' gives [mahar] IMP. -/
def teach : ConsonantalRoot Segment := ⟨[m, h, «ɾ»]⟩

/-- √ħrd 'slaughter' gives [ta-ħarrɨd] 2-IMPRF. -/
def slaughter : ConsonantalRoot Segment := ⟨[ħ, «ɾ», d]⟩

/-- √ħdm 'escape' gives [ta-ħadɨm] 2-IMPRF. -/
def escape : ConsonantalRoot Segment := ⟨[ħ, d, m]⟩

/-- √sʔl 'ask' gives [saʔal] IMP. -/
def ask : ConsonantalRoot Segment := ⟨[s, «ʔ», l]⟩

/-- √glh 'uncover' gives [gɨlah] IMP.M, [gɨlh-i] IMP-F, [mɨ-glah] GER. -/
def uncover : ConsonantalRoot Segment := ⟨[«ɡ», l, h]⟩

/-- √nbħ 'bark' gives [nɨβaħ] IMP.M, [nɨbħ-i] IMP-F, [mɨ-nbaħ] GER. -/
def bark : ConsonantalRoot Segment := ⟨[n, b, ħ]⟩

/-- √bdl 'hurt', a type B verb with medial gemination throughout, gives [bʌddʌl-ʌ] DEP.PRF-3MSG
and [mɨ-bɨddal] GER. -/
def hurt : ConsonantalRoot Segment := ⟨[b, d, l]⟩

/-- √brk 'bless', a type C verb with [a] after the first radical throughout, gives [barʌk-ʌ]
DEP.PRF-3MSG and [mɨ-bɨrak] GER. -/
def bless : ConsonantalRoot Segment := ⟨[b, «ɾ», k]⟩

/-- √ʕrf, unglossed in [faust-lampitelli-2026], gives [ʕarifu] PRF-3MSG, [ʕɨrʌf] IMP and
[ʕarʌf-] DEP.PRF. -/
def arf : ConsonantalRoot Segment := ⟨[«ʕ», «ɾ», f]⟩

end Tigrinya.Phonology
