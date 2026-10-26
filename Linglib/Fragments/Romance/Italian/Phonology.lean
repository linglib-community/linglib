module

public import Linglib.Data.PHOIBLE.Inventories.Italian
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Segmental.Sonority

/-!
# Italian phonemes

This file lists the phonemes of Standard Italian, gives each its segment, and sorts the beginnings
of words by how they select among the variant forms of an article before them. The inventory is
Rogers and d'Arcangeli's: seven vowels and twenty-three consonants, among them the glides /j w/
and the five consonants /ɲ ʃ ʎ ts dz/ that are always long between vowels, also across a word
boundary, which Krämer calls inherently long. Each phoneme names its glyph in the PHOIBLE chart,
and its segment is the segment of that chart entry.

A masculine article takes one form before a vowel, another before an inherently long consonant or
*s* followed by a consonant, and a third before any other consonant or a cluster of rising
sonority, as Krämer sorts them. Maiden and Robustelli add to the second group the palatal glide
and clusters rare at the beginning of a word, such as *ps*, *pt* and *ft*, which `Onset.of` takes
to be the clusters whose sonority does not rise.

## Main definitions

* `Italian.Phonology.a`, `Italian.Phonology.p` and the like: the phonemes.
* `Italian.Phonology.inventory`, `Italian.Phonology.inherentlyLong`.
* `Italian.Phonology.Onset`, `Italian.Phonology.Onset.of`: the beginnings of words.

## Main results

* `Italian.Phonology.subset_ita`: the phonemes are segments of PHOIBLE's Italian inventory.
* `Italian.Phonology.isConsonant_iff`, `Italian.Phonology.ofSegment_eq_liquid_iff` and the like:
  the phonemes fall in the classes `Onset.of` reads.

## Implementation notes

PHOIBLE writes /a/ with the chart glyph `ɐ`. Before a glide the article varies from word to word
and in part follows the spelling (Krämer). `Onset.of` takes [j] as Maiden and Robustelli do, as in
*lo iodio* and *la iena*, and [w] as a vowel, as in *l'uomo*, so that loans such as *il weekend*
are exceptions.

## References

* [rogers-darcangeli-2004]
* [kramer-2009b]
* [maiden-robustelli-2007]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Italian.Phonology

/-! ### Phonemes -/

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The close-mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The open-mid front vowel /ɛ/. -/
def «ɛ» : Segment := .ofChart .«ɛ»

/-- The low central vowel /a/, the glyph `ɐ` of PHOIBLE's inventory. -/
def a : Segment := .ofChart .«ɐ»

/-- The open-mid back rounded vowel /ɔ/. -/
def «ɔ» : Segment := .ofChart .«ɔ»

/-- The close-mid back rounded vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The high back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiceless dental stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiced dental stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar stop /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The palatal nasal /ɲ/. -/
def «ɲ» : Segment := .ofChart .«ɲ»

/-- The alveolar trill /r/. -/
def r : Segment := .ofChart .«r»

/-- The voiceless dental affricate /ts/. -/
def ts : Segment := .ofChart .«ts»

/-- The voiced dental affricate /dz/. -/
def dz : Segment := .ofChart .«dz»

/-- The voiceless postalveolar affricate /tʃ/. -/
def «tʃ» : Segment := .ofChart .«t̠ʃ»

/-- The voiced postalveolar affricate /dʒ/. -/
def «dʒ» : Segment := .ofChart .«d̠ʒ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiced labiodental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless postalveolar fricative /ʃ/. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The alveolar lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The palatal lateral /ʎ/. -/
def «ʎ» : Segment := .ofChart .«ʎ»

/-- The phonemes of Standard Italian ([rogers-darcangeli-2004] p. 117), pairwise distinct. -/
def inventory : Finset Segment :=
  ⟨↑[i, e, «ɛ», a, «ɔ», o, u, p, b, t, d, k, g, m, n, «ɲ», r, ts, dz, «tʃ», «dʒ», f, v, s, z,
    «ʃ», j, w, l, «ʎ»], by decide⟩

theorem subset_ita : inventory ⊆ Inventories.Italian.ita.segments :=
  Inventory.subset_segments_iff.2 (by decide)

theorem isVowel_iff :
    ∀ x ∈ inventory, x.IsVowel ↔ x ∈ ({i, e, «ɛ», a, «ɔ», o, u} : Finset Segment) := by
  decide

theorem isConsonant_iff : ∀ x ∈ inventory, x.IsConsonant ↔ ¬ x.IsVowel ∧ x ≠ j ∧ x ≠ w := by
  decide

theorem ofSegment_eq_nasal_iff :
    ∀ x ∈ inventory, Sonority.ofSegment x = .nasal ↔ x = m ∨ x = n ∨ x = «ɲ» := by
  decide

theorem ofSegment_eq_liquid_iff :
    ∀ x ∈ inventory, Sonority.ofSegment x = .liquid ↔ x = r ∨ x = l ∨ x = «ʎ» := by
  decide

theorem ofSegment_eq_glide_iff :
    ∀ x ∈ inventory, Sonority.ofSegment x = .glide ↔ x = j ∨ x = w := by
  decide

/-- The inherently long consonants, which are long between vowels, also at the beginning of a word
after one ([kramer-2009b] p. 49, [maiden-robustelli-2007] §2.5, p. 10). -/
def inherentlyLong : Finset Segment := {«ɲ», «ʃ», «ʎ», ts, dz}

/-! ### The beginnings of words -/

/-- The beginning of a word, as it selects among the variant forms of an article before it
([kramer-2009b] p. 86, [maiden-robustelli-2007] §4.1, pp. 61–63). -/
inductive Onset where
  /-- A vowel or the labial glide [w], as in *l'orso* and *l'uomo*. -/
  | vowel
  /-- The palatal glide [j], as in *lo iodio*. -/
  | glide
  /-- *s*, pronounced [s] or [z], followed by a consonant, as in *lo spazio*. -/
  | sConsonant
  /-- An inherently long consonant, as in *lo zio*. -/
  | inherentlyLong
  /-- Two consonants whose sonority does not rise, as in *lo psicologo*. -/
  | rareCluster
  /-- Any other consonant or a cluster of rising sonority, as in *il gatto* and *il treno*. -/
  | consonant
  deriving DecidableEq, Fintype, Repr

/-- The beginning of a word, read from its first two segments; a word of fewer than two segments
counts as `consonant`. -/
def Onset.of : List Segment → Onset
  | x :: y :: _ =>
    if x.IsVowel ∨ x = w then .vowel
    else if x = j then .glide
    else if (x = s ∨ x = z) ∧ y.IsConsonant then .sConsonant
    else if x ∈ Phonology.inherentlyLong then .inherentlyLong
    else if y.IsConsonant ∧ ¬ Sonority.ofSegment x < Sonority.ofSegment y then .rareCluster
    else .consonant
  | _ => .consonant

theorem Onset.of_cons_cons (x y : Segment) (rest : List Segment) :
    Onset.of (x :: y :: rest) = Onset.of [x, y] :=
  rfl

example : [[s, p, a], [ts, i, o], [p, s, i], [t, r, a], [g, l, i], [«ʎ», i], [«dʒ», «ɛ»],
    [j, «ɔ»], [w, «ɔ»]].map Onset.of = [.sConsonant, .inherentlyLong, .rareCluster, .consonant,
      .consonant, .inherentlyLong, .consonant, .glide, .vowel] := by
  decide

end Italian.Phonology
