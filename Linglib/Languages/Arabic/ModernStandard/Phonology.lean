module

public import Linglib.Data.PHOIBLE.Inventories.Arabic
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Modern Standard Arabic phonology

This file defines the 28 consonants and the three vowels of Modern Standard Arabic
([ryding-2005]) as segments named by their IPA symbols, with feature values from the PHOIBLE
chart. A long vowel is not a further phoneme here.

The chart entries follow the glyphs of PHOIBLE's Arabic inventory 2157, an urban Levantine
composite, so the coronals are dental and the emphatics are the chart's [+RTR] consonants, which
differ from their plain counterparts in [RTR] alone. The standard language departs from that
inventory in four consonants: /t/ and /k/ are plain where 2157 has aspirated t̪ʰ and kʰ, and the
fricatives خ and غ are the uvular /χ/ and /ʁ/ where 2157 has xʀ̥ and velar ɣ. The inventory's
lˤ is not a phoneme of the standard language. The values /dʒ/ for ج and /ðˤ/ for ظ are those of
[ryding-2005]; corpus transcription traditions write them g and zˤ.

## Main definitions

* `b`, `f`, …, `j`: the consonants, and `consonants`, the set of them.
* `a`, `i`, `u`: the vowels, and `vowels`, the set of them.

## Main results

* `subset_arb`: every consonant but `t`, `k`, `χ` and `ʁ` is a segment of PHOIBLE's
  inventory 2157.

## References

* [ryding-2005]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Arabic.ModernStandard.Phonology

/-- The voiced bilabial stop /b/ (ب). -/
def b : Segment := .ofChart .«b»

/-- The voiceless labiodental fricative /f/ (ف). -/
def f : Segment := .ofChart .«f»

/-- The bilabial nasal /m/ (م). -/
def m : Segment := .ofChart .«m»

/-- The voiceless dental stop /t/ (ت). -/
def t : Segment := .ofChart .«t̪»

/-- The voiced dental stop /d/ (د). -/
def d : Segment := .ofChart .«d̪»

/-- The emphatic voiceless stop /tˤ/ (ط). -/
def «tˤ» : Segment := .ofChart .«t̪̙ˤ»

/-- The emphatic voiced stop /dˤ/ (ض). -/
def «dˤ» : Segment := .ofChart .«d̙ˤ»

/-- The voiceless dental fricative /θ/ (ث). -/
def θ : Segment := .ofChart .«θ̪»

/-- The voiced dental fricative /ð/ (ذ). -/
def ð : Segment := .ofChart .«ð̪»

/-- The emphatic voiced dental fricative /ðˤ/ (ظ). -/
def «ðˤ» : Segment := .ofChart .«ð̪̙ˤ»

/-- The voiceless alveolar fricative /s/ (س). -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative /z/ (ز). -/
def z : Segment := .ofChart .«z»

/-- The emphatic voiceless fricative /sˤ/ (ص). -/
def «sˤ» : Segment := .ofChart .«s̙ˤ»

/-- The voiceless postalveolar fricative /ʃ/ (ش). -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar affricate /dʒ/ (ج). -/
def «dʒ» : Segment := .ofChart .«d̪ʒ»

/-- The voiceless velar stop /k/ (ك). -/
def k : Segment := .ofChart .«k»

/-- The voiceless uvular stop /q/ (ق). -/
def q : Segment := .ofChart .«q»

/-- The voiceless uvular fricative /χ/ (خ). -/
def χ : Segment := .ofChart .«χ»

/-- The voiced uvular fricative /ʁ/ (غ). -/
def «ʁ» : Segment := .ofChart .«ʁ»

/-- The voiceless pharyngeal fricative /ħ/ (ح). -/
def ħ : Segment := .ofChart .«ħ»

/-- The voiced pharyngeal fricative /ʕ/ (ع). -/
def «ʕ» : Segment := .ofChart .«ʕ̙»

/-- The voiceless glottal fricative /h/ (ه). -/
def h : Segment := .ofChart .«h»

/-- The glottal stop /ʔ/ (ء). -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- The lateral /l/ (ل). -/
def l : Segment := .ofChart .«l»

/-- The trill /r/ (ر). -/
def r : Segment := .ofChart .«r»

/-- The dental nasal /n/ (ن). -/
def n : Segment := .ofChart .«n̪»

/-- The labial-velar glide /w/ (و). -/
def w : Segment := .ofChart .«w»

/-- The palatal glide /j/ (ي). -/
def j : Segment := .ofChart .«j»

/-- The consonants of Modern Standard Arabic. -/
def consonants : Finset Segment :=
  ⟨↑[b, f, m, t, d, «tˤ», «dˤ», θ, ð, «ðˤ», s, z, «sˤ», «ʃ», «dʒ», l, r, n, k, q, χ, «ʁ», ħ,
    «ʕ», h, «ʔ», w, j], by decide +kernel⟩

/-- The open vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The close front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The vowels of Modern Standard Arabic. -/
def vowels : Finset Segment := ⟨↑[a, i, u], by decide +kernel⟩

/-- Every consonant but `t`, `k`, `χ` and `ʁ` is a segment of PHOIBLE's inventory 2157. -/
theorem subset_arb : consonants \ {t, k, χ, «ʁ»} ⊆ Inventories.Arabic.arb.segments :=
  Inventory.subset_segments_iff.2 (by decide +kernel)

end Arabic.ModernStandard.Phonology
