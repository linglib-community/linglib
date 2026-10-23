module

public import Linglib.Data.PHOIBLE.Inventories.Tagalog
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.NasalSubstitution

/-!
# Tagalog phonology

This file defines the segments of Tagalog and the two outcomes of a prefix that ends in a nasal,
such as *maŋ-* and *paŋ-*, before a stem.

The nasal is a velar /ŋ/. Before a nasal, a glide or *h* it is unchanged, as in *paŋmarká*, and
before another consonant it takes that consonant's place, as in *pantabój* and *panlabás*.
Before an obstruent there is a second outcome, nasal substitution, in which the nasal and the
obstruent surface as one nasal at the obstruent's place, as in *mamigáj* from *bigáj*. Which
stems substitute is lexical and variable, which is the matter of the studies of Zuraw, of Zuraw
and Hayes and of Magri.

## Main definitions

* `consonants`, `vowels`: the phonemes of Zuraw's inventory.
* `assimilate`: a nasal takes the place of a following non-nasal consonant.
* `cluster`, `substituted`: a prefix in `ŋ` attached to a stem, with assimilation alone and
  with substitution of the stem-initial segment.

## Main results

* `subset_tgl`: the phonemes are those of PHOIBLE's Tagalog inventory.
* `substitute_eq`: each obstruent substitutes to the nasal of its place, and the glottal stop
  to the velar nasal.
* `cluster_of_not_trigger`: the prefix nasal is unchanged before a nasal, a glide or *h*.

## References

* [K. Zuraw, *A model of lexical variation and the grammar with application to Tagalog nasal
  substitution* (2010)][zuraw-2010]
* [zuraw-hayes-2017]
* [magri-2025]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Tagalog

/-! ### Segments -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The glottal stop /ʔ/. -/
def «ʔ» : Segment := .ofChart .«ʔ»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiced velar stop /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The velar nasal /ŋ/. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The rhotic /r/. -/
def r : Segment := .ofChart .«r»

/-- The labial-velar glide /w/. -/
def w : Segment := .ofChart .«w»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The low vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The mid back vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The high back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The consonants, pairwise distinct. -/
def consonants : Finset Segment :=
  ⟨↑[p, t, k, «ʔ», b, d, g, s, h, m, n, ŋ, l, r, w, j], by decide⟩

/-- The vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[i, e, a, o, u], by decide⟩

/-- The phonemes are segments of PHOIBLE's Tagalog inventory. -/
theorem subset_tgl : consonants ∪ vowels ⊆ Inventories.Tagalog.tgl.segments :=
  Inventory.subset_segments_iff.2 (by decide)

/-! ### The prefix nasal -/

/-- The consonants that a preceding nasal assimilates to, which are those that are not nasals.
The glides and `h` are not consonantal. -/
def trigger : Segment := Segment.ofSpecs [(.consonantal, true), (.nasal, false)]

/-- `assimilate w` is the word `w` with each nasal assimilated to a following non-nasal
consonant. -/
def assimilate : List Segment → List Segment := NasalSubstitution.assimilate trigger ŋ

/-- `substitute x` is the nasal that the prefix nasal and a stem-initial `x` surface as under
substitution. -/
def substitute : Segment → List Segment := NasalSubstitution.substitute trigger ŋ

/-- `cluster pre stem` attaches the prefix that consists of `pre` and the nasal to `stem`, with
assimilation of the nasal to the stem-initial segment alone. -/
def cluster (pre : List Segment) : List Segment → List Segment
  | [] => pre ++ [ŋ]
  | x :: rest => pre ++ assimilate [ŋ, x] ++ rest

/-- `substituted pre stem` attaches the prefix that consists of `pre` and the nasal to `stem`,
with substitution of the stem-initial segment. -/
def substituted (pre : List Segment) : List Segment → List Segment
  | [] => pre ++ [ŋ]
  | x :: rest => pre ++ substitute x ++ rest

/-- Each obstruent substitutes to the nasal of its place, and the glottal stop, which has no
place, to the velar nasal. -/
theorem substitute_eq :
    substitute p = [m] ∧ substitute b = [m] ∧ substitute t = [n] ∧ substitute d = [n] ∧
      substitute s = [n] ∧ substitute k = [ŋ] ∧ substitute g = [ŋ] ∧ substitute «ʔ» = [ŋ] := by
  decide

/-- The prefix nasal is unchanged before a nasal, a glide, `h` or a vowel. -/
theorem cluster_of_not_trigger :
    ∀ x ∈ consonants ∪ vowels, ¬ trigger ≤ x → cluster [] [x] = [ŋ, x] := by
  decide

theorem cluster_head_mem :
    ∀ x ∈ consonants, ∀ N ∈ (cluster [] [x]).head?, N ∈ ({m, n, ŋ} : Finset Segment) := by
  decide

/-! ### Examples -/

theorem mamigaj : substituted [m, a] [b, i, g, a, j] = [m, a, m, i, g, a, j] := by decide

theorem pantaboj : cluster [p, a] [t, a, b, o, j] = [p, a, n, t, a, b, o, j] := by decide

theorem pansulat : cluster [p, a] [s, u, l, a, t] = [p, a, n, s, u, l, a, t] := by decide

theorem panlabas : cluster [p, a] [l, a, b, a, s] = [p, a, n, l, a, b, a, s] := by decide

theorem mangulol : substituted [m, a] [«ʔ», u, l, o, l] = [m, a, ŋ, u, l, o, l] := by decide

theorem mapangamkam :
    substituted [m, a, p, a] [k, a, m, k, a, m] = [m, a, p, a, ŋ, a, m, k, a, m] ∧
      assimilate [k, a, m, k, a, m] ≠ [k, a, m, k, a, m] := by
  decide

end Tagalog
