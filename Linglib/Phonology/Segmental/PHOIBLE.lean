module

public import Linglib.Data.PHOIBLE.Chart
public import Linglib.Phonology.Segmental.Basic

/-!
# Segments from PHOIBLE feature matrices

This file turns a PHOIBLE feature matrix into a `Segment`, so that a fragment can take the
feature values of its phonemes from the PHOIBLE chart instead of listing them. PHOIBLE's
features extend those of Hayes, which `Phonology.Feature` follows, with length, tone, stress,
clicks and further laryngeal features. Each feature of `Phonology.Feature` is a PHOIBLE column,
under another name for [voice], [constricted glottis], [ATR] and [RTR], and the segment of a
matrix reads the matrix along that correspondence, dropping the columns it lacks.

The two systems differ in one convention. PHOIBLE specifies [round] only on labial segments
and marks it not applicable elsewhere, where Hayes's charts give every other segment
[−round]. The segment of a matrix therefore takes [−round] as its default.

PHOIBLE also codes the tongue-root contrast of plain vowel glyphs by [tense], /i e o u/
against /ɪ ɛ ɔ ʊ/, and gives every plain vowel [−ATR]; only glyphs with the diacritic ◌̘ are
[+ATR]. A language whose vowels contrast in [ATR] reads a chart entry through its tongue-root
reading, which carries the [tense] value as the [ATR] value.

A fragment gives each phoneme by `Segment.ofChart`. It reads a chart entry, merges over it
the values on which a grammar departs from the chart, and keeps the result on the features
the grammar treats as contrastive. A phoneme is then a segment, named by its symbol, and an
inventory is a finite set of segments, which a fragment shows to lie among the segments of a
PHOIBLE inventory.

## Main definitions

* `Phonology.Feature.toPHOIBLE`: the PHOIBLE column of each feature.
* `Data.PHOIBLE.FeatureMatrix.toSegment`: the segment of a feature matrix.
* `Data.PHOIBLE.FeatureMatrix.tenseAsATR`: the tongue-root reading of a feature matrix.
* `Data.PHOIBLE.Inventory.segments`: the segments of an inventory's phonemes.
* `Phonology.Segment.ofChart`: the segment of a chart entry, a departure and a contrastive
  feature set.

## Main results

* `Phonology.Feature.toPHOIBLE_injective`: distinct features are distinct columns.
* `Data.PHOIBLE.FeatureMatrix.range_toSegment`: the segments of feature matrices are those
  specified for [round].
* `Phonology.Segment.ofChart_apply`: on a contrastive feature where the departure is silent,
  the segment has the chart's value.

## Implementation notes

Dropping PHOIBLE's further features can identify two phonemes of an inventory, a long and a
short vowel or a plain and a fortis stop, which then have one segment. A fragment guards
against this by giving its inventory as a list of segments with a proof that it has no
duplicates. PHOIBLE also leaves [round] unspecified on its less-rounded segments, written
with ◌̜, which therefore come out [−round]. Velar consonants are [−front, −back] in PHOIBLE,
so a vowel tier is picked out by `Segment.IsVowel` and not by the absence of a [back] value.

## References

* [moran-mccloy-2019]
* [hayes-2009]
-/

@[expose] public section

namespace Phonology.Feature

/-- The PHOIBLE column of a feature. -/
def toPHOIBLE : Feature → Data.PHOIBLE.Feature
  | .syllabic => .syllabic
  | .consonantal => .consonantal
  | .sonorant => .sonorant
  | .approximant => .approximant
  | .continuant => .continuant
  | .delayedRelease => .delayedRelease
  | .nasal => .nasal
  | .lateral => .lateral
  | .strident => .strident
  | .tap => .tap
  | .trill => .trill
  | .voice => .periodicGlottalSource
  | .spreadGlottis => .spreadGlottis
  | .constrGlottis => .constrictedGlottis
  | .labial => .labial
  | .round => .round
  | .labiodental => .labiodental
  | .coronal => .coronal
  | .anterior => .anterior
  | .distributed => .distributed
  | .dorsal => .dorsal
  | .high => .high
  | .low => .low
  | .front => .front
  | .back => .back
  | .tense => .tense
  | .atr => .advancedTongueRoot
  | .rtr => .retractedTongueRoot

theorem toPHOIBLE_injective : Function.Injective toPHOIBLE := by decide

end Phonology.Feature

namespace Data.PHOIBLE.FeatureMatrix

open Phonology

/-- The segment of a feature matrix reads the matrix along `Feature.toPHOIBLE`, with [−round]
where PHOIBLE marks [round] not applicable. -/
def toSegment (m : FeatureMatrix) : Segment :=
  Function.update (m ∘ Phonology.Feature.toPHOIBLE) .round ((m .round).unbotD false : Bool)

theorem toSegment_apply_of_ne_round (m : FeatureMatrix) {f : Phonology.Feature}
    (h : f ≠ .round) : m.toSegment f = m f.toPHOIBLE :=
  Function.update_of_ne h ..

@[simp] theorem toSegment_round (m : FeatureMatrix) :
    m.toSegment .round = ((m .round).unbotD false : Bool) :=
  Function.update_self ..

/-- The segments of feature matrices are exactly those specified for [round], since each other
feature of `Phonology.Feature` is a column of its own. -/
theorem range_toSegment : Set.range toSegment = {s : Segment | s .round ≠ ⊥} := by
  refine Set.ext fun s ↦ ⟨by rintro ⟨m, rfl⟩; simp, fun hs ↦ ?_⟩
  refine ⟨Function.extend Phonology.Feature.toPHOIBLE s ⊥, funext fun f ↦ ?_⟩
  have he := Phonology.Feature.toPHOIBLE_injective.extend_apply s ⊥ f
  obtain rfl | hf := eq_or_ne f .round
  · obtain ⟨b, hb⟩ := Flat.ne_bot_iff_exists.1 hs
    simp only [Phonology.Feature.toPHOIBLE] at he
    rw [toSegment_round, he, hb, Flat.unbotD_coe]
  · rw [toSegment_apply_of_ne_round _ hf, he]

/-! ### The tongue-root reading -/

/-- The tongue-root reading of a matrix carries its [tense] value as its tongue-root value,
keeping its own tongue-root value where it has no [tense], and has no [tense]. -/
def tenseAsATR (m : FeatureMatrix) : FeatureMatrix :=
  Function.update (Function.update m .advancedTongueRoot ((m .tense).or (m .advancedTongueRoot)))
    .tense ⊥

@[simp] theorem toSegment_tenseAsATR_atr (m : FeatureMatrix) :
    m.tenseAsATR.toSegment .atr = (m .tense).or (m .advancedTongueRoot) := by
  rw [toSegment_apply_of_ne_round _ (by decide), Phonology.Feature.toPHOIBLE, tenseAsATR,
    Function.update_of_ne (by decide), Function.update_self]

@[simp] theorem toSegment_tenseAsATR_tense (m : FeatureMatrix) :
    m.tenseAsATR.toSegment .tense = ⊥ := by
  rw [toSegment_apply_of_ne_round _ (by decide), Phonology.Feature.toPHOIBLE, tenseAsATR,
    Function.update_self]

theorem toSegment_tenseAsATR_of_ne (m : FeatureMatrix) {f : Phonology.Feature} (ha : f ≠ .atr)
    (ht : f ≠ .tense) : m.tenseAsATR.toSegment f = m.toSegment f := by
  have ht' : f.toPHOIBLE ≠ .tense := Phonology.Feature.toPHOIBLE_injective.ne ht
  have ha' : f.toPHOIBLE ≠ .advancedTongueRoot := Phonology.Feature.toPHOIBLE_injective.ne ha
  obtain rfl | hr := eq_or_ne f .round
  · simp [tenseAsATR]
  · rw [toSegment_apply_of_ne_round _ hr, toSegment_apply_of_ne_round _ hr, tenseAsATR,
      Function.update_of_ne ht', Function.update_of_ne ha']

/-! ### Witnesses from the chart -/

/-- An unrounded vowel is [−round] and a rounded one keeps its [+round]. -/
example : «i».toSegment.HasValue .round false ∧ «u».toSegment.HasValue .round true := by decide

/-- A velar stop is [−back], so the absence of a [back] value does not pick out
consonants. -/
example : «k».toSegment.HasValue .back false := by decide

/-- A long vowel differs from its short counterpart only in [long], which `Phonology.Feature`
lacks, so the two have one segment. -/
example : «aː».toSegment = «a».toSegment ∧ «aː» ≠ «a» := by decide

/-- The chart makes /i/ [−ATR]. Its tongue-root reading makes /i/ [+ATR] and /ɪ/ [−ATR], and
leaves the low vowel, which has no [tense], at the chart's [−ATR]. -/
example : «i».toSegment.HasValue .atr false ∧ «i».tenseAsATR.toSegment.HasValue .atr true ∧
    «ɪ».tenseAsATR.toSegment.HasValue .atr false ∧
    «a».tenseAsATR.toSegment.HasValue .atr false := by
  decide

end Data.PHOIBLE.FeatureMatrix

namespace Data.PHOIBLE.Inventory

open Phonology

/-- The segments of an inventory's phonemes. -/
def segments (I : Inventory) : Finset Segment := I.featureMatrices.image FeatureMatrix.toSegment

@[simp] theorem mem_segments {I : Inventory} {s : Segment} :
    s ∈ I.segments ↔ ∃ y ∈ I.phonemes, y.features.toSegment = s := by
  simp [segments]

theorem subset_segments_iff {I : Inventory} {S : Finset Segment} :
    S ⊆ I.segments ↔ ∀ x ∈ S, ∃ y ∈ I.phonemes, y.features.toSegment = x :=
  subset_image_featureMatrices_iff

end Data.PHOIBLE.Inventory

namespace Phonology.Segment

open Data.PHOIBLE

/-- The segment of a chart entry `m` has the values of `departure` where that is specified and
those of `m` elsewhere, kept on the features in `contrastive`. -/
def ofChart (m : FeatureMatrix) (departure : Segment := ⊥)
    (contrastive : Finset Feature := Finset.univ) : Segment :=
  Segment.restrict contrastive fun f ↦ (departure f).or (m.toSegment f)

theorem ofChart_apply {m : FeatureMatrix} {departure : Segment} {contrastive : Finset Feature}
    {f : Feature} (hf : f ∈ contrastive) (hd : departure f = ⊥) :
    ofChart m departure contrastive f = m.toSegment f := by
  rw [ofChart, Segment.restrict, Finset.piecewise_eq_of_mem _ _ _ hf, hd, Flat.bot_or]

@[simp] theorem ofChart_eq_toSegment (m : FeatureMatrix) : ofChart m = m.toSegment :=
  funext fun f ↦ ofChart_apply (Finset.mem_univ f) rfl

end Phonology.Segment
