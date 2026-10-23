module

public import Linglib.Data.PHOIBLE.Inventories.Indonesian
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.NasalSubstitution

/-!
# Indonesian phonology

This file defines the segments of Standard Indonesian and the alternation of the nasal that
ends the prefixes *meN-* and *peN-*.

The nasal is a velar /ŋ/. It takes the place of a following obstruent, as in *membeli* from
*beli*, and it is lost before a nasal, a liquid or a glide, as in *melihat* from *lihat*. A
root-initial *p*, *t*, *k* or *s* fuses with it into one nasal, as in *memakai* from *pakai*,
which is called nasal substitution. Following Pater, assimilation applies throughout the word
and fusion only at the left edge of the root.

## Main definitions

* `consonants`, `vowels`: the phonemes, named by their spelling. `e` is the schwa and `é` is /e/.
* `assimilate`: each nasal of a word takes the place of a following obstruent, by the rules of
  `Phonology/NasalSubstitution.lean`.
* `substituting`, `fuse`: the consonants that fuse with the prefix nasal, and the nasal that
  results.
* `juncture`: what the prefix nasal and the base-initial segment surface as.
* `meN`, `peN`: the two prefixes attached to a base.

## Main results

* `subset_ind`: the phonemes are those of PHOIBLE's Standard Indonesian inventory.

## Implementation notes

That *c* does not fuse and that *s* fuses into the palatal *ny* are the two exceptions that
McDonnell and colleagues list for the standard language. The *menge-* of one-syllable bases is
not defined.

## References

* [J. N. Sneddon, *Indonesian: A comprehensive grammar* (1996)][sneddon-1996]
* [B. McDonnell, J. Wu, T. McKinnon and A. Adelaar, *Malayic languages*
  (2024)][mcdonnell-wu-mckinnon-adelaar-2024]
* [M. Donohue, *Phonotactics and morphophonology* (2024)][donohue-2024]
* [J. Pater, *Austronesian nasal substitution revisited: what's wrong with \*NC (and what's
  not)* (2001)][pater-2001]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Indonesian.Phonology

/-! ### Segments -/

/-- The voiceless bilabial stop `p`. -/
def p : Segment := .ofChart .«p»

/-- The voiced bilabial stop `b`. -/
def b : Segment := .ofChart .«b»

/-- The voiceless alveolar stop `t`. -/
def t : Segment := .ofChart .«t»

/-- The voiced alveolar stop `d`. -/
def d : Segment := .ofChart .«d»

/-- The voiceless postalveolar affricate `c`, /tʃ/. -/
def c : Segment := .ofChart .«t̠ʃ»

/-- The voiced postalveolar affricate `j`, /dʒ/. -/
def j : Segment := .ofChart .«d̠ʒ»

/-- The voiceless velar stop `k`. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar stop `g`. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless labiodental fricative `f`, in loans. -/
def f : Segment := .ofChart .«f»

/-- The voiceless alveolar fricative `s`. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative `z`, in loans. -/
def z : Segment := .ofChart .«z»

/-- The voiceless postalveolar fricative `sy`, /ʃ/, in loans. -/
def sy : Segment := .ofChart .«ʃ»

/-- The voiceless velar fricative `kh`, /x/, in loans. -/
def kh : Segment := .ofChart .«x»

/-- The glottal fricative `h`. -/
def h : Segment := .ofChart .«h»

/-- The bilabial nasal `m`. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal `n`. -/
def n : Segment := .ofChart .«n»

/-- The palatal nasal `ny`, /ɲ/. -/
def ny : Segment := .ofChart .«ɲ»

/-- The velar nasal `ng`, /ŋ/. -/
def ng : Segment := .ofChart .«ŋ»

/-- The lateral `l`. -/
def l : Segment := .ofChart .«l»

/-- The trill `r`. -/
def r : Segment := .ofChart .«r»

/-- The labial-velar glide `w`. -/
def w : Segment := .ofChart .«w»

/-- The palatal glide `y`, /j/. -/
def y : Segment := .ofChart .«j»

/-- The high front vowel `i`. -/
def i : Segment := .ofChart .«i»

/-- The high back vowel `u`. -/
def u : Segment := .ofChart .«u»

/-- The mid front vowel `é`, /e/, spelled *e*. -/
def é : Segment := .ofChart .«e»

/-- The schwa `e`, /ə/. -/
def e : Segment := .ofChart .«ə»

/-- The mid back vowel `o`. -/
def o : Segment := .ofChart .«o»

/-- The low vowel `a`. -/
def a : Segment := .ofChart .«a»

/-- The consonants, pairwise distinct. -/
def consonants : Finset Segment :=
  ⟨↑[p, b, t, d, c, j, k, g, f, s, z, sy, kh, h, m, n, ny, ng, l, r, w, y], by decide⟩

/-- The vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[i, u, é, e, o, a], by decide⟩

/-- Every phoneme but the palatal glide is a segment of PHOIBLE's Standard Indonesian
inventory. -/
theorem subset_ind : (consonants ∪ vowels).erase y ⊆ Inventories.Indonesian.ind.segments :=
  Inventory.subset_segments_iff.2 (by decide)

/-! ### Natural classes -/

/-- The segments that a preceding nasal assimilates to, which are the obstruents. The glottal
`h` is not consonantal. -/
def trigger : Segment := Segment.ofSpecs [(.consonantal, true), (.sonorant, false)]

/-- The sonorant consonants, [+sonorant, −syllabic], which are the nasals, liquids and
glides. -/
def sonorantConsonant : Segment := Segment.ofSpecs [(.sonorant, true), (.syllabic, false)]

/-! ### Nasal assimilation -/

/-- `assimilate w` is the word `w` with each nasal assimilated to a following obstruent. -/
def assimilate : List Segment → List Segment := NasalSubstitution.assimilate trigger ng

/-! ### Nasal substitution -/

/-- The root-initial consonants that fuse with the prefix nasal. -/
def substituting : Finset Segment := {p, t, k, s}

/-- What the prefix nasal and a root-initial `x` fuse into, which is the assimilated nasal,
except that with `s` it is the palatal `ny`. -/
def fuse (x : Segment) : List Segment :=
  if x = s then [ny] else NasalSubstitution.substitute trigger ng x

/-- What the prefix nasal and the base-initial segment `x` surface as. A substituting
consonant fuses with the nasal, the nasal is lost before a sonorant consonant, and otherwise it
assimilates. -/
def juncture (x : Segment) : List Segment :=
  if x ∈ substituting then fuse x
  else if sonorantConsonant ≤ x then [x]
  else assimilate [ng, x]

/-- `prefixN pre base` attaches to `base` the prefix that consists of `pre` and the nasal. -/
def prefixN (pre : List Segment) : List Segment → List Segment
  | [] => pre ++ [ng]
  | x :: rest => pre ++ juncture x ++ rest

/-- The verbal prefix *meN-*. -/
def meN : List Segment → List Segment := prefixN [m, e]

/-- The nominal prefix *peN-*. -/
def peN : List Segment → List Segment := prefixN [p, e]

end Indonesian.Phonology
