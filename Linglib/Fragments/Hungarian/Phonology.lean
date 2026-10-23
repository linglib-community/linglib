module

public import Linglib.Data.PHOIBLE.Inventories.Hungarian
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Harmony.System

/-!
# Hungarian phonology

This file gives the short vowels and the consonants of Hungarian as segments, reads spelled
words as segments, classifies the vowels for harmony, and states the two harmony systems the
suffix alternations follow. The seven vowels are those of
Siptár and Törkenczy's vowel system, and a long vowel has the features of its short
counterpart, length being prosodic. In their classification the front unrounded vowels are
neutral, the front rounded vowels front harmonic, and the back vowels back harmonic. Palatal
harmony spreads the backness of the last harmonic stem vowel rightward through the transparent
neutral vowels. Rounding harmony spreads the rounding of the last stem vowel, and resolves the
three-way suffixes. Both are systems in the sense of Rose and Walker's decomposition.

The feature values come from the PHOIBLE chart, read at the short vowels of PHOIBLE's
Hungarian inventory and kept on the features the system (7) uses. The short low vowel is the
chart's rounded [ɒ], and Siptár and Törkenczy class it with the unrounded back vowels, its
rounding being a matter of phonetic implementation, so it departs from the chart in [round].
The consonants are the chart's segments of the consonants of the inventory, each with all its
features. A spelled word is read grapheme by grapheme, each digraph such as ⟨sz⟩ or ⟨ny⟩ and the
trigraph ⟨dzs⟩ being one grapheme, and an accented vowel letter writes a long vowel.

## Main definitions

* `Hungarian.contrastive`: the features the vowel system uses.
* `Hungarian.i`, `Hungarian.epsilon` and the like: the seven short vowels, and
  `Hungarian.vowels` the set of them.
* `Hungarian.p`, `Hungarian.«ɲ»` and the like: the consonants, and `Hungarian.consonants` the set of
  them.
* `Hungarian.graphemes`, `Hungarian.ofGrapheme`, `Hungarian.transcribe?`: the graphemes of a spelled
  word and the segments they write; `Hungarian.ofLetter` the vowel a letter writes.
* `Hungarian.IsLong`, `Hungarian.longPositions`: the graphemes that write long vowels, and the
  positions of a spelled word at which they stand.
* `Hungarian.palatalHarmony`, `Hungarian.labialHarmony`: the two harmony systems.

## Main results

* `Hungarian.subset_hun`, `Hungarian.consonants_subset_hun`: each vowel's chart entry, and each
  consonant, is in PHOIBLE's Hungarian inventory.
* `Hungarian.isNeutral_iff`, `Hungarian.isFrontHarmonic_iff`, `Hungarian.isBackHarmonic_iff`:
  the neutral vowels are /i/ and /ɛ/, the front harmonic ones /y/ and /ø/, and the rest are
  back harmonic.

## Implementation notes

* Antiharmonic stems, vacillating stems and the height-graded transparency of the neutral
  vowels are not properties of these systems: `Studies/SiptarTorkenczy2000` derives them from
  the book's place-feature analysis.

## References

* [siptar-torkenczy-2000]
* [rose-walker-2011]
* [moran-mccloy-2019]
-/

@[expose] public section

namespace Hungarian

open Phonology Phonology.Harmony Data.PHOIBLE

/-! ### The vowel inventory -/

/-- The features the vowel system (7) uses, with [syllabic] marking the vowels. -/
def contrastive : Finset Phonology.Feature := {.syllabic, .high, .low, .back, .round}

/-- A vowel is its chart entry's segment, with its departure, on the contrastive features. -/
def vowel (m : FeatureMatrix) (departure : Segment := ⊥) : Segment :=
  .ofChart m departure contrastive

/-- The high front unrounded vowel /i/, orthographic ⟨i⟩. -/
def i : Segment := vowel .«i»

/-- The high front rounded vowel /y/, orthographic ⟨ü⟩. -/
def y : Segment := vowel .«y»

/-- The high back vowel /u/. -/
def u : Segment := vowel .«u»

/-- The front unrounded vowel /ɛ/, orthographic ⟨e⟩. -/
def epsilon : Segment := vowel .«ɛ»

/-- The mid front rounded vowel /ø/, orthographic ⟨ö⟩. -/
def ø : Segment := vowel .«ø»

/-- The mid back vowel /o/. -/
def o : Segment := vowel .«o»

/-- The low back vowel /ɒ/, orthographic ⟨a⟩, which departs from the chart in being phonologically
unrounded. -/
def turnedScriptA : Segment := vowel .«ɒ» (Segment.ofSpecs [(.round, false)])

/-- The seven short vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[i, y, u, epsilon, ø, o, turnedScriptA], by decide⟩

theorem subset_hun :
    vowels.erase turnedScriptA ⊆ Inventories.Hungarian.hun.featureMatrices.image vowel ∧
      FeatureMatrix.«ɒ» ∈ Inventories.Hungarian.hun.featureMatrices :=
  ⟨Inventory.subset_image_featureMatrices_iff.2 (by decide),
    Inventory.mem_featureMatrices.2 (by decide)⟩

/-! ### The consonants -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiceless palatal stop, orthographic ⟨ty⟩, the chart's affricated `cç`. -/
def «cç» : Segment := .ofChart .«cç»

/-- The voiced palatal stop, orthographic ⟨gy⟩, the chart's affricated `ɟʝ`. -/
def «ɟʝ» : Segment := .ofChart .«ɟʝ»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar stop /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless alveolar affricate /ts/, orthographic ⟨c⟩. -/
def ts : Segment := .ofChart .«ts»

/-- The voiced alveolar affricate /dz/. -/
def dz : Segment := .ofChart .«dz»

/-- The voiceless postalveolar affricate /t̠ʃ/, orthographic ⟨cs⟩. -/
def «t̠ʃ» : Segment := .ofChart .«t̠ʃ»

/-- The voiced postalveolar affricate /d̠ʒ/, orthographic ⟨dzs⟩. -/
def «d̠ʒ» : Segment := .ofChart .«d̠ʒ»

/-- The voiceless labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The voiced labiodental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The voiceless alveolar fricative /s/, orthographic ⟨sz⟩. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless postalveolar fricative /ʃ/, orthographic ⟨s⟩. -/
def «ʃ» : Segment := .ofChart .«ʃ»

/-- The voiced postalveolar fricative /ʒ/, orthographic ⟨zs⟩. -/
def «ʒ» : Segment := .ofChart .«ʒ»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The palatal nasal /ɲ/, orthographic ⟨ny⟩. -/
def «ɲ» : Segment := .ofChart .«ɲ»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The trill /r/. -/
def r : Segment := .ofChart .«r»

/-- The palatal glide /j/, orthographic ⟨j⟩ and ⟨ly⟩. -/
def j : Segment := .ofChart .«j»

/-- The consonants, pairwise distinct. -/
def consonants : Finset Segment :=
  ⟨↑[p, b, t, d, «cç», «ɟʝ», k, g, ts, dz, «t̠ʃ», «d̠ʒ», f, v, s, z, «ʃ», «ʒ», h, m, n, «ɲ», l, r,
    j], by decide⟩

theorem consonants_subset_hun : consonants ⊆ Inventories.Hungarian.hun.segments :=
  Inventory.subset_segments_iff.2 (by decide)

/-! ### Spelling -/

/-- The graphemes of a spelled word are its letters, with each digraph and the trigraph ⟨dzs⟩
read as one grapheme. -/
def graphemes : List Char → List (List Char)
  | 'd' :: 'z' :: 's' :: cs => ['d', 'z', 's'] :: graphemes cs
  | 'c' :: 's' :: cs => ['c', 's'] :: graphemes cs
  | 'd' :: 'z' :: cs => ['d', 'z'] :: graphemes cs
  | 'g' :: 'y' :: cs => ['g', 'y'] :: graphemes cs
  | 'l' :: 'y' :: cs => ['l', 'y'] :: graphemes cs
  | 'n' :: 'y' :: cs => ['n', 'y'] :: graphemes cs
  | 's' :: 'z' :: cs => ['s', 'z'] :: graphemes cs
  | 't' :: 'y' :: cs => ['t', 'y'] :: graphemes cs
  | 'z' :: 's' :: cs => ['z', 's'] :: graphemes cs
  | c :: cs => [c] :: graphemes cs
  | [] => []

/-- The segment a grapheme writes, a long vowel writing the segment of its short counterpart. -/
def ofGrapheme : List Char → Option Segment
  | ['i'] | ['í'] => some i
  | ['ü'] | ['ű'] => some y
  | ['u'] | ['ú'] => some u
  | ['e'] | ['é'] => some epsilon
  | ['ö'] | ['ő'] => some ø
  | ['o'] | ['ó'] => some o
  | ['a'] | ['á'] => some turnedScriptA
  | ['p'] => some p | ['b'] => some b | ['t'] => some t | ['d'] => some d
  | ['t', 'y'] => some «cç» | ['g', 'y'] => some «ɟʝ» | ['k'] => some k | ['g'] => some g
  | ['c'] => some ts | ['d', 'z'] => some dz | ['c', 's'] => some «t̠ʃ»
  | ['d', 'z', 's'] => some «d̠ʒ» | ['f'] => some f | ['v'] => some v | ['s', 'z'] => some s
  | ['z'] => some z | ['s'] => some «ʃ» | ['z', 's'] => some «ʒ» | ['h'] => some h
  | ['m'] => some m | ['n'] => some n | ['n', 'y'] => some «ɲ» | ['l'] => some l
  | ['r'] => some r | ['j'] | ['l', 'y'] => some j
  | _ => none

/-- The vowel written by an orthographic vowel letter, long and short alike. -/
def ofLetter (letter : String) : Option Segment :=
  (ofGrapheme letter.toList).filter fun x ↦ decide x.IsVowel

/-- The vowels of a word written as a list of orthographic segments. -/
def vowelsOf (segments : List String) : List Segment := segments.filterMap ofLetter

/-- A grapheme writes a long vowel when it carries an acute or double acute accent. -/
def IsLong (gr : List Char) : Prop := gr ∈ [['í'], ['ű'], ['ú'], ['é'], ['ő'], ['ó'], ['á']]

instance : DecidablePred IsLong := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The segments a spelled word writes, if every grapheme writes one. -/
def transcribe? (w : String) : Option (List Segment) := (graphemes w.toList).mapM ofGrapheme

/-- The positions of a spelled word at which it writes a long vowel. -/
def longPositions (w : String) : Finset ℕ :=
  (((graphemes w.toList).zipIdx).filter fun x ↦ decide (IsLong x.1)).map (·.2) |>.toFinset

/-! ### Harmonic classification -/

/-- A vowel is neutral when it is front and unrounded. -/
def IsNeutral (s : Segment) : Prop :=
  s.HasValue .syllabic true ∧ s.HasValue .back false ∧ s.HasValue .round false

/-- A vowel is front harmonic when it is front and rounded. -/
def IsFrontHarmonic (s : Segment) : Prop :=
  s.HasValue .syllabic true ∧ s.HasValue .back false ∧ s.HasValue .round true

/-- Every back vowel is back harmonic. -/
def IsBackHarmonic (s : Segment) : Prop := s.HasValue .syllabic true ∧ s.HasValue .back true

instance : DecidablePred IsNeutral := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsFrontHarmonic := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsBackHarmonic := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem isNeutral_iff : ∀ x ∈ vowels, IsNeutral x ↔ x = i ∨ x = epsilon := by decide

theorem isFrontHarmonic_iff : ∀ x ∈ vowels, IsFrontHarmonic x ↔ x = y ∨ x = ø := by decide

theorem isBackHarmonic_iff :
    ∀ x ∈ vowels, IsBackHarmonic x ↔ x = u ∨ x = o ∨ x = turnedScriptA := by
  decide

/-! ### The harmony systems -/

/-- Palatal harmony spreads the backness of the last harmonic stem vowel rightward to the
suffix vowels unspecified for it, consonants and the neutral vowels being off the tier. -/
def palatalHarmony : System Segment :=
  System.mk' (feature := .back)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .back = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true ∨ IsNeutral s)
    (direction := .rightward)

/-- Rounding harmony spreads the rounding of the last stem vowel to the suffix vowels
unspecified for it, with no transparent vowels; it matters only for front stems, since a
back stem takes the back alternant of a three-way suffix. -/
def labialHarmony : System Segment :=
  System.mk' (feature := .round)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .round = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true)
    (direction := .rightward)

end Hungarian
