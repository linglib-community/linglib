module

public import Linglib.Data.PHOIBLE.Inventories.Finnish
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Harmony.System
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Finnish phonology

This file gives Finnish phonemes as segments and states palatal harmony and consonant
gradation over them. In Karlsson's description the vowels fall into three classes. The back
vowels /ɑ o u/ and the front vowels /æ ø y/, written ⟨a o u⟩ and ⟨ä ö y⟩, do not mix within a
word, and the neutral vowels /e i/ occur with either set. A suffix vowel alternates with the
stem, so that the partitive is *kirja-a* 'book' but *käsi-ä* 'hand', and the inessive
*talo-ssa* 'in the house' but *metsä-ssä* 'in the forest'. Harmony is a single system in the
sense of Rose and Walker. The feature [back] spreads rightward from the last harmonic stem
vowel to suffix vowels unspecified for it, consonants and the neutral vowels are transparent,
and a stem with no harmonic vowel takes front suffixes.

The feature values come from the PHOIBLE chart, read at the vowels of a PHOIBLE Finnish
inventory and kept on the features that distinguish the eight vowels. The alternating suffix
vowel is the meet of /ɑ/ and /æ/, the features they share, and so has no value for [back].
Phonemes are named by their letters, so a list of them reads as the word is spelled.

Karlsson writes the vowel of the illative -Vn and of the passive personal ending as `V`, a
vowel that is the same as the nearest vowel before it, as in *talo-on* 'into the house' and
*tie-hen* 'to the road'. `V` is a vowel with no other feature, and it copies each quality
feature from that vowel before harmony applies. When the nearest vowel is the suffix vowel,
as in *luke-ma-an* 'to read', `V` is left without [back] and harmony gives both the same
value.

Consonant gradation, the second of Karlsson's two important sound alternations, weakens a
stop at the onset of a syllable that an ending closes. The long stops shorten, *kukka*
'flower' but *kuka-n*, which is quantitative gradation, and the short stops change, *katu*
'street' but *kadu-lla*, *tupa* 'hut' but *tuva-ssa*, *tauko* 'pause' but *tauo-n*, which is
qualitative gradation. By Karlsson's rule A the ending consists of one consonant or begins
with two, and only a short vowel stands between the stop and the ending, so that *katto*
'roof' gives *kato-n* and *kato-lla* but *katto-na*.

## Main definitions

* `Finnish.a`, `Finnish.k` and the like: the vowels and the consonants of the example forms,
  and `Finnish.vowels`, `Finnish.consonants` the sets of them.
* `Finnish.A`, `Finnish.O`: the alternating suffix vowels.
* `Finnish.V`, `Finnish.C`: the copy vowel, which as a rule context is any vowel, and any
  consonant.
* `Finnish.palatalHarmony`, `Finnish.vowelCopy`: palatal harmony and the copying of `V`.
* `Finnish.surface`: the surface form of a word, vowel copy followed by harmony.
* `Finnish.ofChar`, `Finnish.ofString?`: the phonemes that a letter and a word write.
* `Finnish.consonantGradation`: the qualitative rules followed by the quantitative ones.

## Main results

* `Finnish.subset_fin`: the vowels are those of PHOIBLE's Finnish inventory.
* `Finnish.isNeutral_iff`, `Finnish.isBackVowel_iff`: the neutral vowels are /e i/ and the
  back vowels /ɑ o u/.
* `Finnish.naturalClass_A`: the natural class of the suffix vowel is /ɑ æ/.
* `Finnish.unspecified_back_A`, `Finnish.setFeature_back_A`: the suffix vowel has no [back],
  and with [back] filled in it is /ɑ/ or /æ/.
* `Finnish.sourceValue_back`: a back stem vowel is the source across a neutral one, and a
  stem of neutral vowels has no source.
* `Finnish.unspecified_round_iff`, `Finnish.hasValue_syllabic_consonants`: `V` is the only
  vowel without [round], and every consonant is [−syllabic], as vowel copy requires.
* `Finnish.surface_suffix`: the suffix vowel after back, front and neutral stems, and `V`
  after a vowel and after the suffix vowel.
* `Finnish.katto`: Karlsson's paradigm of *katto*, gradation in *katon*, *katolla* and
  *katolta* and none in *kattona*.
* `Finnish.quantitative_gradation`, `Finnish.qualitative_gradation`: his examples of the two
  types.

## Implementation notes

The inventory is PHOIBLE 2535, which transcribes the low back vowel [ɑ] and the mid vowels
with lowering diacritics. The consonants take plain chart glyphs, which that inventory
writes with place diacritics, so membership is stated for the vowels only.

Consonant gradation belongs to the lexicon, since many words do not undergo it (*auto-ssa*
'in the car'), so `surface` leaves it out and a stem is given in the grade its ending
selects, as in Karlsson's segmentations *pöydä-llä* and *käde-ssä*. A search copies one
feature, so vowel copy is four searches. `V` is the only vowel without [round]
(`unspecified_round_iff`), so the targets of each search are the vowels without it and [round]
is copied last.

A rule has one right context, so each alternation is two rules, one for an ending of a
single consonant and one for an ending that begins with two. The qualitative rules apply
first, since the short stop that quantitative gradation leaves does not weaken again. The
qualitative rules are stated after a vowel, and that of /t/ also after /h/. A long stop is two
segments, and so is a long vowel, which the rules do not yet tell from a short one.

## TODO

* The alternations of /p/ and /k/ after /l r/ and the assimilations after a nasal or liquid,
  Karlsson's types (8) to (12), the rare types (13) to (16), the ban on gradation
  before a long vowel, and rule B for verbs.

## References

* [karlsson-2017]
* [rose-walker-2011]
* [goldsmith-1976]
* [moran-mccloy-2019]
-/

@[expose] public section

namespace Finnish

open Phonology Phonology.Harmony Subregular.LocalRewrite Data.PHOIBLE

/-! ### Phonemes

A phoneme is named by its letter, so `a` is ɑ, `ä` is æ and `ö` is ø. -/

/-- The features that distinguish the vowels, with [syllabic] marking them as vowels. -/
def contrastive : Finset Phonology.Feature := {.syllabic, .high, .low, .back, .round}

/-- A vowel is its chart entry's segment on the contrastive features. -/
def vowel (m : FeatureMatrix) : Segment := .ofChart m ⊥ contrastive

/-- The low back vowel /ɑ/. -/
def a : Segment := vowel .«ɑ»

/-- The mid back vowel /o/. -/
def o : Segment := vowel .«o̞»

/-- The high back vowel /u/. -/
def u : Segment := vowel .«u»

/-- The low front vowel /æ/. -/
def ä : Segment := vowel .«æ»

/-- The mid front rounded vowel /ø/. -/
def ö : Segment := vowel .«ø̞»

/-- The high front rounded vowel /y/. -/
def y : Segment := vowel .«y»

/-- The mid front unrounded vowel /e/. -/
def e : Segment := vowel .«e̞»

/-- The high front unrounded vowel /i/. -/
def i : Segment := vowel .«i»

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The labiodental /v/. -/
def v : Segment := .ofChart .«v»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The trill /r/. -/
def r : Segment := .ofChart .«r»

/-- The eight vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[a, o, u, ä, ö, y, e, i], by decide⟩

/-- The consonants of the example forms, pairwise distinct. -/
def consonants : Finset Segment := ⟨↑[p, t, k, d, s, n, v, l, j, m, h, r], by decide⟩

theorem subset_fin : vowels ⊆ Inventories.Finnish.fin.featureMatrices.image vowel :=
  Inventory.subset_image_featureMatrices_iff.2 (by decide)

/-- `A` is the vowel of the alternating suffixes such as the essive -nA and the partitive -A.
It is what `a` and `ä` share. -/
def A : Segment := a ⊓ ä

/-- `O` is the vowel of the interrogative clitic -kO. It is what `o` and `ö` share. -/
def O : Segment := o ⊓ ö

/-- `V` is the vowel of the illative -Vn, a vowel with no other feature. As a rule context it
is any vowel. -/
def V : Segment := Segment.ofSpecs [(.syllabic, true)]

/-- `C`, as a rule context, is any consonant. -/
def C : Segment := Segment.ofSpecs [(.syllabic, false)]

/-! ### Harmonic classification -/

/-- A back vowel is [+syllabic, +back]. -/
def IsBackVowel (s : Segment) : Prop := s.IsVowel ∧ s.HasValue .back true

/-- A neutral vowel is front, unrounded and non-low, and is transparent to harmony. -/
def IsNeutral (s : Segment) : Prop :=
  s.IsVowel ∧ s.HasValue .back false ∧ s.HasValue .round false ∧ s.HasValue .low false

instance : DecidablePred IsBackVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsNeutral := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem isNeutral_iff : ∀ x ∈ vowels, IsNeutral x ↔ x = e ∨ x = i := by decide

theorem isBackVowel_iff : ∀ x ∈ vowels, IsBackVowel x ↔ x = a ∨ x = o ∨ x = u := by decide

/-! ### The harmony system -/

/-- Finnish palatal harmony spreads [back] from the last harmonic stem vowel to the suffix
vowels unspecified for it, and a stem with no harmonic vowel takes front suffixes by default.
Consonants and the neutral vowels /e i/ are off the tier. -/
def palatalHarmony : System Segment :=
  System.mk' (feature := .back)
    (IsTarget := fun s ↦ s.IsVowel ∧ s.Unspecified .back)
    (IsTransparent := fun s ↦ ¬ s.IsVowel ∨ IsNeutral s)
    (direction := .rightward)
    (default := some false)

/-- The copying of the feature `f` into `V` from the nearest vowel before it. Consonants are
off the tier, and the targets are the vowels without [round], which `V` alone is. -/
def copyToV (f : Phonology.Feature) : System Segment :=
  System.mk' (feature := f)
    (IsTarget := fun s ↦ s.IsVowel ∧ s.Unspecified .round)
    (IsTransparent := fun s ↦ ¬ s.IsVowel)

theorem unspecified_round_iff : ∀ x ∈ vowels ∪ {A, O, V}, x.Unspecified .round ↔ x = V := by
  decide

theorem hasValue_syllabic_consonants : ∀ x ∈ consonants, x.HasValue .syllabic false := by
  decide

/-- Vowel copy gives `V` the quality of the nearest vowel before it, [round] last. -/
def vowelCopy (w : List Segment) : List Segment :=
  [Phonology.Feature.back, .high, .low, .round].foldl (fun w f ↦ (copyToV f).searchCopy.apply w) w

/-- The surface form of a word is reached by copying a vowel into `V` and then letting palatal
harmony fill the suffix vowels. -/
def surface (w : List Segment) : List Segment := palatalHarmony.searchCopy.apply (vowelCopy w)

theorem naturalClass_A : A.naturalClass vowels = {a, ä} := by decide

theorem unspecified_back_A : A.Unspecified .back := by decide

theorem setFeature_back_A : A.setFeature .back true = a ∧ A.setFeature .back false = ä := by
  decide

theorem sourceValue_back :
    palatalHarmony.searchCopy.sourceValue [a] = some true ∧
      palatalHarmony.searchCopy.sourceValue [a, i] = some true ∧
      palatalHarmony.searchCopy.sourceValue [ä] = some false ∧
      palatalHarmony.searchCopy.sourceValue [e, i] = none := by
  decide

theorem surface_suffix :
    surface [t, a, l, o, s, s, A] = [t, a, l, o, s, s, a] ∧
      surface [k, y, l, ä, s, s, A] = [k, y, l, ä, s, s, ä] ∧
      surface [t, i, e, s, s, A] = [t, i, e, s, s, ä] ∧
      surface [t, a, l, o, V, n] = [t, a, l, o, o, n] ∧
      surface [t, i, e, h, V, n] = [t, i, e, h, e, n] ∧
      surface [t, a, l, o, n, A, V, n] = [t, a, l, o, n, a, a, n] := by
  decide

/-! ### Spelling -/

/-- `ofChar c` is the phoneme that the letter `c` writes. A long vowel or stop is written
double. -/
def ofChar : Char → Option Segment
  | 'a' => some a | 'o' => some o | 'u' => some u | 'ä' => some ä | 'ö' => some ö
  | 'y' => some y | 'e' => some e | 'i' => some i | 'p' => some p | 't' => some t
  | 'k' => some k | 'd' => some d | 's' => some s | 'n' => some n | 'v' => some v
  | 'l' => some l | 'j' => some j | 'm' => some m | 'h' => some h | 'r' => some r
  | _ => none

/-- `ofString? w` is the phonemes that the word `w` writes, if its letters all write one. -/
def ofString? (w : String) : Option (List Segment) := w.toList.mapM ofChar

/-! ### Consonant gradation -/

/-- The rules weakening `target` after `left`, before a short vowel and an ending that is one
consonant or begins with two. -/
def gradation (target : Segment) (effect : Effect) (left : ContextElem) : List Rule :=
  [[.seg V, .seg C, .wordBoundary], [.seg V, .seg C, .seg C]].map fun right ↦
    { target, effect, leftContext := [left], rightContext := right }

/-- In qualitative gradation /p/ becomes /v/ and /k/ is lost after a vowel, and /t/ becomes
/d/ after a vowel and after /h/. -/
def qualitativeGradation : List Rule :=
  let voice : Effect := .changeFeatures (Segment.ofSpecs [(.voice, true)])
  gradation p (.replace v) (.seg V) ++ gradation t voice (.seg V) ++ gradation t voice (.seg h) ++
    gradation k .delete (.seg V)

/-- In quantitative gradation a long stop loses its second half. -/
def quantitativeGradation : List Rule :=
  [p, t, k].flatMap fun c ↦ gradation c .delete (.seg c)

/-- Consonant gradation is the qualitative rules followed by the quantitative ones. -/
def consonantGradation : List Rule := qualitativeGradation ++ quantitativeGradation

theorem katto :
    derive consonantGradation [k, a, t, t, o, n] = [k, a, t, o, n] ∧
      derive consonantGradation [k, a, t, t, o, l, l, a] = [k, a, t, o, l, l, a] ∧
      derive consonantGradation [k, a, t, t, o, l, t, a] = [k, a, t, o, l, t, a] ∧
      derive consonantGradation [k, a, t, t, o, n, a] = [k, a, t, t, o, n, a] := by
  decide

theorem quantitative_gradation :
    derive consonantGradation [k, a, a, p, p, i, s, s, a] = [k, a, a, p, i, s, s, a] ∧
      derive consonantGradation [k, u, k, k, a, n] = [k, u, k, a, n] := by
  decide

theorem qualitative_gradation :
    derive consonantGradation [t, u, p, a, s, s, a] = [t, u, v, a, s, s, a] ∧
      derive consonantGradation [k, a, t, u, l, l, a] = [k, a, d, u, l, l, a] ∧
      derive consonantGradation [l, ä, h, t, e, n] = [l, ä, h, d, e, n] ∧
      derive consonantGradation [t, a, u, k, o, n] = [t, a, u, o, n] := by
  decide

end Finnish
