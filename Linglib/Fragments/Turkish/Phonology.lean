module

public import Linglib.Data.PHOIBLE.Inventories.Turkish
public import Linglib.Phonology.Harmony.System
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Segmental.Sonority.Basic
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Turkish phonology

This file defines the segments of Turkish, the alternations of its suffixes and the surface
form of a suffixed word, following the reference grammar of [goksel-kerslake-2005].

The phonemes are segments named by their letters, with feature values from the PHOIBLE chart.
The eight vowels differ in [high], [back] and [round]. A suffix vowel is an archiphoneme, the
meet of its alternants: `A` is what `a` and `e` share and lacks [back], and `I` is what the four
high vowels share and lacks [back] and [round]. The suffix-initial `D` and `C` lack [voice].

For a harmonized string `w` and a segment `x`, `fill w x` is `x` with [back], [round] and
[voice] taken from `w` where `x` lacks them, and `harmonize` fills a word in from left to right.
Before -(I)yor a stem-final `a` or `e` is raised (`raising`), and `surface` applies the raising
and then harmonizes. `fronting`, `rounding` and `voicing` state the three alternations as
harmony systems.

## Implementation notes

A vowel keeps the chart's values for the features that distinguish the eight vowels, together
with [voice]. Among consonants [back] is contrastive only on the palatal lateral of loans such
as *gol*, so every other consonant keeps each chart value but [back], as in the analysis of
[clements-sezer-1982]. The inventory is PHOIBLE 2217, whose `a` is central where the grammar's
is back. `K` is `k` without a value for [continuant] and not a meet, since the meet of `k` and
`ğ` would lack [voice] and so be a target of voicing. The raised vowel harmonizes for rounding
as well as backness, as in *okşuyor*, so raising replaces the stem vowel by `I`. The letters
*f*, *ğ* and *j* write segments outside the inventory and have no value under `ofChar`. That
the search-and-copy rules of the three systems compute the harmonized form is proved in
`Studies/GokselKerslake2005.lean`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [G. N. Clements and E. Sezer, *Vowel and consonant disharmony in Turkish*][clements-sezer-1982]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
-/

@[expose] public section

open Phonology Phonology.Harmony Subregular.LocalRewrite Data.PHOIBLE

namespace Turkish.Phonology

/-! ### Segments -/

/-- A vowel is its chart entry's segment, with its departure, on the major class features, which
mark it as a vowel, the features that distinguish the eight vowels, and [voice]. -/
def vowel (m : FeatureMatrix) (departure : Segment := ⊥) : Segment :=
  .ofChart m departure (Sonority.features ∪ {.voice, .high, .back, .round})

/-- A consonant is its chart entry's segment on every feature but [back], which is contrastive
among consonants on the palatal lateral alone. -/
def consonant (m : FeatureMatrix) : Segment := .ofChart m ⊥ {.back}ᶜ

/-- The low back vowel `a`, a back vowel where the chart's is central: the grammar describes [a]
as "a low, back and unrounded vowel" (§1.1.2.1). -/
def a : Segment := vowel .«a» [+back]

/-- The non-high front unrounded vowel `e`. -/
def e : Segment := vowel .«e»

/-- The high back unrounded vowel `ı`, /ɯ/. -/
def ı : Segment := vowel .«ɯ»

/-- The high front unrounded vowel `i`. -/
def i : Segment := vowel .«i»

/-- The non-high back rounded vowel `o`. -/
def o : Segment := vowel .«o»

/-- The non-high front rounded vowel `ö`, /œ/. -/
def ö : Segment := vowel .«œ»

/-- The high back rounded vowel `u`. -/
def u : Segment := vowel .«u»

/-- The high front rounded vowel `ü`, /y/. -/
def ü : Segment := vowel .«y»

/-- The voiceless bilabial stop `p`. -/
def p : Segment := consonant .«p»

/-- The voiced bilabial stop `b`. -/
def b : Segment := consonant .«b»

/-- The voiceless dental stop `t`. -/
def t : Segment := consonant .«t̪»

/-- The voiced dental stop `d`. -/
def d : Segment := consonant .«d̪»

/-- The voiceless velar stop `k`. -/
def k : Segment := consonant .«k»

/-- The voiced velar stop `g`. -/
def g : Segment := consonant .«ɡ»

/-- The voiced postalveolar affricate `c`, /dʒ/. -/
def c : Segment := consonant .«d̠ʒ»

/-- The voiceless postalveolar affricate `ç`, /tʃ/. -/
def ç : Segment := consonant .«t̠ʃ»

/-- The voiceless dental fricative `s`. -/
def s : Segment := consonant .«s̪»

/-- The voiced dental fricative `z`. -/
def z : Segment := consonant .«z̪»

/-- The voiceless postalveolar fricative `ş`, /ʃ/. -/
def ş : Segment := consonant .«ʃ»

/-- The voiced labiodental fricative `v`. -/
def v : Segment := consonant .«v»

/-- The glottal fricative `h`. -/
def h : Segment := consonant .«h»

/-- The bilabial nasal `m`. -/
def m : Segment := consonant .«m»

/-- The dental nasal `n`. -/
def n : Segment := consonant .«n̪»

/-- The lateral `l`. -/
def l : Segment := consonant .«l»

/-- The tap `r`, /ɾ/. -/
def r : Segment := consonant .«ɾ»

/-- The palatal glide `y`, /j/. -/
def y : Segment := consonant .«j»

/-- The palatal `l'` of loans such as *gol* and *hal*, which shares the chart entry of `l` and
is [−back] (§3.4 (iv)). -/
def l' : Segment := .ofChart .«l» [−back]

/-- The vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[a, e, ı, i, o, ö, u, ü], by decide⟩

/-- The consonants, pairwise distinct. -/
def consonants : Finset Segment :=
  ⟨↑[p, b, t, d, k, g, c, ç, s, z, ş, v, h, m, n, l, l', r, y], by decide⟩

/-- Every phoneme but `a` and the two laterals is a segment of PHOIBLE's Turkish inventory,
and the chart entry of `a` is in that inventory. -/
theorem subset_tur :
    vowels.erase a ⊆ Inventories.Turkish.tur.featureMatrices.image vowel ∧
      consonants \ {l, l'} ⊆ Inventories.Turkish.tur.featureMatrices.image consonant ∧
      FeatureMatrix.«a» ∈ Inventories.Turkish.tur.featureMatrices :=
  ⟨Inventory.subset_image_featureMatrices_iff.2 (by decide),
    Inventory.subset_image_featureMatrices_iff.2 (by decide),
    Inventory.mem_featureMatrices.2 (by decide)⟩

/-- `A` is the vowel of A-type suffixes such as -lAr and -mA. It is what `a` and `e` share,
unrounded and non-high, and fronting harmony supplies its backness (§3.2.2). -/
def A : Segment := a ⊓ e

/-- `I` is the vowel of I-type suffixes such as -(I)m and -mIş. It is what the four high
vowels share, and the two harmonies supply its backness and rounding (§3.2.1). -/
def I : Segment := ı ⊓ i ⊓ u ⊓ ü

/-- `D` is the suffix-initial stop of -DI and -DA, which is `t` after a voiceless consonant
and `d` otherwise (§6.1.2). It is what `t` and `d` share. -/
def D : Segment := t ⊓ d

/-- `C` is the suffix-initial affricate of -CI, which is `ç` after a voiceless consonant and `c`
otherwise (§6.1.2). It is what `ç` and `c` share. -/
def C : Segment := ç ⊓ c

/-- `K` is the final consonant of -(y)AcAK, which is `k`, or `ğ` before a vowel (Chapter 2). It
is `k` without a value for [continuant]. -/
def K : Segment := Segment.restrict {.continuant}ᶜ k

/-- A consonant lacks a value for [back] unless it is the palatal lateral, which is what
fronting's tier test reads. -/
theorem back_eq_bot_iff : ∀ x ∈ consonants, x .back = none ↔ x ≠ l' := by decide

/-- Every phoneme has a value for [voice], so that only `D` and `C` are targets of voicing. -/
theorem voice_ne_bot : ∀ x ∈ vowels ∪ consonants, ¬ x .voice = none := by
  decide

/-- The natural class of a vowel archiphoneme among the vowels, and of `D` or `C` among the
consonants, is its alternants. -/
theorem naturalClass_archiphoneme :
    naturalClass A vowels = {a, e} ∧ naturalClass I vowels = {ı, i, u, ü} ∧
      naturalClass D consonants = {t, d} ∧ naturalClass C consonants = {c, ç} := by
  decide

/-- `A` with [back] filled in is `a` or `e`. -/
theorem setFeature_back_A :
    A.setFeature .back true = a ∧ A.setFeature .back false = e := by
  decide

/-- `D` with [voice] filled in is `d` or `t`. -/
theorem setFeature_voice_D :
    D.setFeature .voice true = d ∧ D.setFeature .voice false = t := by
  decide

/-- `C` with [voice] filled in is `c` or `ç`. -/
theorem setFeature_voice_C :
    C.setFeature .voice true = c ∧ C.setFeature .voice false = ç := by
  decide

/-! ### Alternations -/

/-- Under fronting harmony a suffix vowel unspecified for [back] takes the value of the
preceding segment specified for it, a vowel or a palatal `l'`. All other consonants are off
the tier (§3.1, §3.2). -/
def fronting : System Segment :=
  System.mk' (feature := .back)
    (IsTarget      := fun s ↦ s .syllabic = true ∧ s .back = none)
    (IsTransparent := fun s ↦ s .back = none ∧ ¬ s .syllabic = true)

/-- Under rounding harmony a high suffix vowel unspecified for [round] takes the value of the
preceding vowel. Consonants are off the tier (§3.1, §3.2.1). -/
def rounding : System Segment :=
  System.mk' (feature := .round)
    (IsTarget      := fun s ↦ s .syllabic = true ∧ s .high = true ∧
      s .round = none)
    (IsTransparent := fun s ↦ ¬ s .syllabic = true)

/-- A suffix-initial `D` or `C` takes the [voice] of the preceding segment (§6.1.2). -/
def voicing : System Segment :=
  System.mk' (feature := .voice)
    (IsTarget      := fun s ↦ s .voice = none)
    (IsTransparent := fun _ ↦ False)

/-! ### Raising before -(I)yor -/

/-- A stem-final `a` or `e` becomes high before -(I)yor and then harmonizes, so that *anla-*
gives *anlıyor* and the negative -mA gives -mIyor (§8.2.2, §8.2.3.3). The raised vowel is the
archiphoneme `I`. -/
def raising : Rule where
  target := A
  effect := .replace I
  rightContext := [.seg y, .seg o, .seg r]

/-! ### Surface forms -/

/-- `fill w x` is the segment `x` as it stands after the harmonized string `w`. A syllabic
segment lacking [back] takes it from the last segment of `w` that is syllabic or bears [back],
a high syllabic segment lacking [round] takes it from the last syllabic segment of `w`, and a
segment lacking [voice] takes it from the last segment of `w` (§3.2, §6.1.2). -/
def fill (w : List Segment) (x : Segment) : Segment :=
  let x := if x.IsSyllabic ∧ x .back = none then
    x.copy .back (w.filter fun s ↦ s.IsSyllabic ∨ s .back ≠ none).getLast? else x
  let x := if x.IsSyllabic ∧ x .high = true ∧ x .round = none then
    x.copy .round (w.filter (·.IsSyllabic)).getLast? else x
  if x .voice = none then x.copy .voice w.getLast? else x

/-- `harmonize w` supplies the features that the archiphonemes of `w` lack, each segment
filled in after the harmonized segments before it. -/
def harmonize (w : List Segment) : List Segment := w.foldl (fun h x ↦ h ++ [fill h x]) []

/-- The surface form of an underlying word applies raising before -(I)yor and then harmonizes
it. -/
def surface (w : List Segment) : List Segment := harmonize (raising.apply w)

@[simp] theorem harmonize_nil : harmonize [] = [] := rfl

theorem harmonize_concat (w : List Segment) (x : Segment) :
    harmonize (w ++ [x]) = harmonize w ++ [fill (harmonize w) x] := by
  simp [harmonize, List.foldl_append]

theorem harmonize_append (w t : List Segment) :
    harmonize (w ++ t) = t.foldl (fun h x ↦ h ++ [fill h x]) (harmonize w) :=
  List.foldl_append

@[simp] theorem length_harmonize (w : List Segment) : (harmonize w).length = w.length := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih => simp [harmonize_concat, ih]

/-- The surface form of a word has its length, since no rule deletes or inserts. -/
@[simp] theorem length_surface (w : List Segment) : (surface w).length = w.length := by
  simp [surface, Rule.length_apply (show raising.effect ≠ .delete by simp [raising])]

/-! ### Spelling -/

/-- `ofChar c` is the phoneme that the letter `c` writes. The palatal `l'` is spelled like
`l` and so is the value of no letter. -/
def ofChar : Char → Option Segment
  | 'a' => some a | 'e' => some e | 'ı' => some ı | 'i' => some i
  | 'o' => some o | 'ö' => some ö | 'u' => some u | 'ü' => some ü
  | 'p' => some p | 'b' => some b | 't' => some t | 'd' => some d | 'k' => some k
  | 'g' => some g | 'c' => some c | 'ç' => some ç | 's' => some s | 'z' => some z | 'ş' => some ş
  | 'v' => some v | 'h' => some h | 'm' => some m | 'n' => some n | 'l' => some l
  | 'r' => some r | 'y' => some y
  | _ => none

/-- `ofString? s` is the string of segments that the spelled word `s` writes, if every letter
writes one. -/
def ofString? (s : String) : Option (List Segment) := s.toList.mapM ofChar

/-- `ofSegmented? s` reads a word written with its morpheme boundaries marked `-` and its clitic
boundaries `=`, as glossed examples print it, dropping the boundaries. -/
def ofSegmented? (s : String) : Option (List Segment) :=
  (s.toList.filter fun c ↦ c ≠ '-' ∧ c ≠ '=').mapM ofChar

end Turkish.Phonology
