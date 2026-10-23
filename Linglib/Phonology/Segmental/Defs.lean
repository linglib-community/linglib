/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Piecewise
public import Linglib.Core.Order.Flat

/-!
# Segments and features

This file defines the distinctive features and the segments built over them. The features are
the twenty-six of Hayes's charts and the tongue-root features [ATR] and [RTR]. Hayes names
[ATR] but leaves it off his charts, noting that it is unclear whether it is the same feature as
[tense]; it is a feature of its own here. [long] and [stress], which Hayes also names, are not
features here: length is a segment on two timing slots, and stress belongs to syllables. A
segment gives each feature the value `+`, `−` or none, and segments are ordered by specificity,
with the unspecified segment least and the meet of two segments the description they share.

The file also names some natural classes by their features and defines the sonority hierarchy
of Hayes's Table 4.1, whose five classes are cut by four features, together with Parker's
refinement of it into eight classes. The theorems are in `Phonology/Segmental/Basic.lean`.

## References

* [hayes-2009]: the features of ch. 4 and Table 4.7, the tongue-root feature (p. 83), the
  sonority hierarchy of Table 4.1 (p. 76) and its manner classes (p. 77)
* [halle-vaux-wolfe-2000]: [ATR] and [RTR]
* [parker-2002]: the eight sonority classes
-/

@[expose] public section

namespace Phonology

/-! ### Features -/

/-- A distinctive feature. -/
inductive Feature where
  /-- [+syllabic] segments are syllable nuclei. -/
  | syllabic
  /-- [+consonantal] segments are the liquids, nasals and obstruents. -/
  | consonantal
  /-- [−sonorant] segments, the stops, fricatives and affricates, build up air pressure in the
  vocal tract. -/
  | sonorant
  /-- [+approximant] segments are the liquids, glides and vowels. -/
  | approximant
  /-- [−continuant] segments, the stops, affricates and nasals, close the oral tract fully. -/
  | continuant
  /-- [+delayed release] segments, the affricates and fricatives, have frication noise. -/
  | delayedRelease
  /-- [+nasal] segments are the nasal consonants and the nasalized vowels. -/
  | nasal
  /-- [+lateral] segments let air pass around the side of the tongue. -/
  | lateral
  /-- [+strident] segments are the sibilants, coronal fricatives and affricates whose airstream
  is channelled through a groove in the tongue blade. -/
  | strident
  /-- [+tap] distinguishes taps from the other rhotics. -/
  | tap
  /-- [+trill] distinguishes trills from the other rhotics. -/
  | trill
  /-- [+voice] segments have vocal cord vibration. -/
  | voice
  /-- [+spread glottis] segments, such as [h] and aspirated stops, have a wide glottis. -/
  | spreadGlottis
  /-- [+constricted glottis] segments, such as the glottal stop and ejectives, have a narrow or
  closed glottis. -/
  | constrGlottis
  /-- [+labial] segments are articulated with the lips. -/
  | labial
  /-- [+round] segments are articulated with rounded lips. -/
  | round
  /-- [+labiodental] segments are articulated by touching the lower lip to the upper teeth. -/
  | labiodental
  /-- [+coronal] segments are articulated with the tongue blade or tip. -/
  | coronal
  /-- [+anterior] coronals are articulated at the alveolar ridge or further forward. -/
  | anterior
  /-- [+distributed] coronals are laminal, made with the tongue blade, and [−distributed] ones
  apical. -/
  | distributed
  /-- [+dorsal] segments are articulated with the tongue body. -/
  | dorsal
  /-- [+high] vowels and dorsals have the tongue body raised. -/
  | high
  /-- [+low] vowels and dorsals have the tongue body lowered. -/
  | low
  /-- [+front] vowels and dorsals are front; central ones are [−front, −back]. -/
  | front
  /-- [+back] vowels and dorsals are back; central ones are [−front, −back]. -/
  | back
  /-- [tense] divides the high and the mid vowels in two, [−tense] ones being lax. -/
  | tense
  /-- [+ATR] segments have the tongue root advanced. -/
  | atr
  /-- [+RTR] segments have the tongue root retracted. -/
  | rtr
  deriving DecidableEq, Repr

namespace Feature

/-- All features, in declaration order. -/
def allFeatures : List Feature :=
  [.syllabic, .consonantal, .sonorant, .approximant,
   .continuant, .delayedRelease, .nasal, .lateral, .strident, .tap, .trill,
   .voice, .spreadGlottis, .constrGlottis,
   .labial, .round, .labiodental,
   .coronal, .anterior, .distributed,
   .dorsal, .high, .low, .front, .back, .tense, .atr, .rtr]

instance : Fintype Feature where
  elems := ⟨allFeatures, by decide⟩
  complete f := by cases f <;> decide

end Feature

/-! ### Segments -/

/-- A segment: each feature `+`, `−` or unspecified, ordered by specificity. -/
abbrev Segment := Feature → Flat Bool

namespace Segment

variable (s : Segment)

/-- `s.HasValue f v` holds when `s` gives `f` the value `v`. -/
def HasValue (f : Feature) (v : Bool) : Prop := s f = some v

instance (f : Feature) (v : Bool) : Decidable (s.HasValue f v) :=
  inferInstanceAs (Decidable (_ = _))

/-- `s.Unspecified f` holds when `s` gives `f` no value. -/
def Unspecified (f : Feature) : Prop := s f = none

instance (f : Feature) : Decidable (s.Unspecified f) := inferInstanceAs (Decidable (_ = none))

/-- The segment with the values of a list of feature-value pairs, unspecified for the features
the list omits. -/
def ofSpecs (specs : List (Feature × Bool)) : Segment := fun f ↦ specs.lookup f

/-! ### Natural classes -/

/-- A vowel is a [+syllabic] segment. -/
def IsVowel : Prop := s.HasValue .syllabic true
instance : Decidable s.IsVowel := inferInstanceAs (Decidable (s.HasValue _ _))

/-- A consonant is a [+consonantal] segment. -/
def IsConsonant : Prop := s.HasValue .consonantal true
instance : Decidable s.IsConsonant := inferInstanceAs (Decidable (s.HasValue _ _))

/-- An obstruent is a [+consonantal, −sonorant] segment. -/
def IsObstruent : Prop := s.HasValue .consonantal true ∧ s.HasValue .sonorant false
instance : Decidable s.IsObstruent := inferInstanceAs (Decidable (_ ∧ _))

/-- A nasal is a [+nasal] segment, consonant or vowel. -/
def IsNasal : Prop := s.HasValue .nasal true
instance : Decidable s.IsNasal := inferInstanceAs (Decidable (s.HasValue _ _))

/-- A sibilant is a [+strident] segment. -/
def IsSibilant : Prop := s.HasValue .strident true
instance : Decidable s.IsSibilant := inferInstanceAs (Decidable (s.HasValue _ _))

/-! ### Changes -/

/-- The segment with feature `f` set to `v`, whatever its value before. -/
def setFeature (f : Feature) (v : Bool) : Segment := Function.update s f (some v)

/-- The segment kept on the features in `C` and unspecified on the rest. -/
def restrict (C : Finset Feature) (s : Segment) : Segment := C.piecewise s ⊥

end Segment

/-- The classification of a segment as a consonant or a vowel. -/
inductive Segment.Class where
  /-- A consonant. -/
  | consonant
  /-- A vowel. -/
  | vowel
  deriving DecidableEq, Repr, Fintype

/-- A segment is a vowel when [+syllabic] and a consonant otherwise. -/
def Segment.toClass (s : Segment) : Segment.Class :=
  if s.IsVowel then .vowel else .consonant

/-! ### Sonority -/

/-- The sonority hierarchy, from least to most sonorous. -/
inductive Sonority where
  /-- The obstruents, [−sonorant]. -/
  | obstruent
  /-- The nasals, [−approximant, +sonorant]. -/
  | nasal
  /-- The liquids, [+consonantal, +approximant]. -/
  | liquid
  /-- The glides, [−syllabic, −consonantal]. -/
  | glide
  /-- The vowels, [+syllabic]. -/
  | vowel
  deriving DecidableEq, Repr, Fintype

namespace Sonority

/-- The position of a class on the hierarchy, the obstruents at 0. -/
def rank : Sonority → ℕ
  | .obstruent => 0 | .nasal => 1 | .liquid => 2 | .glide => 3 | .vowel => 4

instance : LinearOrder Sonority :=
  LinearOrder.lift' rank fun a b h ↦ by cases a <;> cases b <;> simp_all [rank]

/-- The column of a class in Table 4.1: its values for [syllabic], [consonantal], [approximant]
and [sonorant], the four features that cut the hierarchy. -/
def toSegment : Sonority → Segment
  | .obstruent =>
    .ofSpecs [(.syllabic, false), (.consonantal, true), (.approximant, false), (.sonorant, false)]
  | .nasal =>
    .ofSpecs [(.syllabic, false), (.consonantal, true), (.approximant, false), (.sonorant, true)]
  | .liquid =>
    .ofSpecs [(.syllabic, false), (.consonantal, true), (.approximant, true), (.sonorant, true)]
  | .glide =>
    .ofSpecs [(.syllabic, false), (.consonantal, false), (.approximant, true), (.sonorant, true)]
  | .vowel =>
    .ofSpecs [(.syllabic, true), (.consonantal, false), (.approximant, true), (.sonorant, true)]

/-- The sonority of a segment: an obstruent if [−sonorant], else a nasal if [−approximant], else
a liquid if [+consonantal], else a vowel if [+syllabic], and otherwise a glide. A syllabic liquid
or nasal keeps the sonority of its class. -/
def ofSegment (s : Segment) : Sonority :=
  if s.HasValue .sonorant false then .obstruent
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-! ### Parker's classes -/

/-- The eight sonority classes of Parker, which split the obstruents by [continuant] and
[voice]. -/
inductive Class where
  /-- The voiceless stops. -/
  | vls
  /-- The voiced stops. -/
  | vds
  /-- The voiceless fricatives. -/
  | vlf
  /-- The voiced fricatives. -/
  | vdf
  /-- The nasals. -/
  | nasal
  /-- The liquids. -/
  | liquid
  /-- The glides. -/
  | glide
  /-- The vowels. -/
  | vowel
  deriving DecidableEq, Repr

namespace Class

-- UNVERIFIED: Parker 2002 not opened; the order of `vds` above `vlf` is from secondary sources.
/-- Parker's ranking of the classes, with voiced stops above voiceless fricatives. -/
def parkerRank : Class → ℕ
  | .vls => 1 | .vlf => 2 | .vds => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

/-- The voiceless obstruent classes. -/
def Voiceless (c : Class) : Prop := c = .vls ∨ c = .vlf

instance : DecidablePred Voiceless := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The class of a segment: its sonority, with an obstruent split by [continuant] and
[voice]. -/
def ofSegment (s : Segment) : Class :=
  match Sonority.ofSegment s with
  | .obstruent =>
    if s.HasValue .continuant true then
      if s.HasValue .voice true then .vdf else .vlf
    else
      if s.HasValue .voice true then .vds else .vls
  | .nasal => .nasal
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel

/-- The sonority of a class, with the obstruents merged. -/
def toSonority : Class → Sonority
  | .vls | .vds | .vlf | .vdf => .obstruent
  | .nasal => .nasal
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel

end Class

end Sonority

end Phonology
