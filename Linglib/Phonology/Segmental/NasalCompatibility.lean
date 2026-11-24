module

public import Linglib.Phonology.Segmental.Sonority.Basic
public import Mathlib.Order.Interval.Set.Basic
import Linglib.Phonology.Segmental.PHOIBLE

/-!
# The nasalization hierarchy

`Phonology.NasalCompatibility` is the hierarchy of segment classes by their compatibility with
nasalization: obstruent stops, fricatives, liquids, glides, glottals, vowels and sonorant stops, a
linear order. `NasalCompatibility.ofSegment` reads the class of a segment off its place features
and [consonantal], [sonorant], [continuant], [approximant] and [syllabic].

Nasal harmonies differ in the classes that nasality spreads through, and in general a class that
undergoes implies every more compatible class. The targets of a harmony are then given by a cut
`c` on the hierarchy: `c.IsTarget s` holds when the class of `s` lies in
`Set.Ico c sonorantStop`, the classes from `c` up short of the sonorant stops, which are nasal
already. The cut at the glides takes the segments that are [−consonantal] and the glottals.

## Main definitions

* `Phonology.NasalCompatibility`: the classes of the hierarchy, with their linear order.
* `Phonology.NasalCompatibility.ofSegment`: the class of a segment.
* `Phonology.NasalCompatibility.IsTarget`: the segments that a harmony with a given cut spreads
  through.
* `Phonology.NasalCompatibility.toSonority`: the sonority of a class.

## Main results

* `Phonology.NasalCompatibility.IsTarget.of_le`: a segment at least as compatible as a target,
  and not a sonorant stop, is a target.
* `Phonology.NasalCompatibility.isTarget_glide_iff`: the cut at the glides takes the segments
  that are [−consonantal] and the glottals.
* `Phonology.NasalCompatibility.monotoneOn_toSonority`,
  `Phonology.NasalCompatibility.not_monotone_toSonority`: sonority rises with compatibility
  among the classes other than the glottals and the sonorant stops, and not among all classes.

## Implementation notes

* The scale of nasalized segments in [walker-2000] has six classes. The glottals stand between
  the glides and the vowels as in her summary of the survey, where they are in parentheses: in
  most languages nasality spreads through them when it spreads through vocoids.
* The linear order is the general classification. The survey also has languages in which
  glottals block where glides undergo, the glottals patterning there with the obstruents;
  languages that differ in the relative order of voiced stops and voiceless fricatives; and
  vowels that block by their height. None of these is represented.
* A glottal is a segment with none of the places [labial], [coronal] and [dorsal]. The chart
  has the glottal stop [+consonantal] and [h] [−consonantal], so [consonantal] does not pick
  the class out.
* A sonorant stop is read off [−approximant], as the nasals of `Phonology.Sonority.ofSegment`
  are, where [walker-2000] writes [+sonorant, −continuant].

## References

* [R. Walker, *Nasalization, Neutral Segments, and Opacity Effects* (2000)][walker-2000]
* [S. Rose and R. Walker, *Harmony systems* (2011)][rose-walker-2011]
-/

@[expose] public section

namespace Phonology

/-- The nasalization hierarchy, from the class least compatible with nasalization to the most. -/
inductive NasalCompatibility where
  /-- The obstruent stops, [+consonantal, −sonorant] and not [+continuant]. -/
  | obstruentStop
  /-- The fricatives, [+consonantal, −sonorant, +continuant]. -/
  | fricative
  /-- The liquids, [+consonantal, +sonorant, +approximant]. -/
  | liquid
  /-- The glides, [−consonantal] with a place and not [+syllabic]. -/
  | glide
  /-- The glottals, [−labial, −coronal, −dorsal]. -/
  | glottal
  /-- The vowels, [−consonantal, +syllabic] with a place. -/
  | vowel
  /-- The sonorant stops, [+consonantal, +sonorant, −approximant]: the nasal stops. -/
  | sonorantStop
  deriving DecidableEq, Repr, Fintype

namespace NasalCompatibility

/-- The position of a class on the hierarchy, the obstruent stops at 0. -/
def rank : NasalCompatibility → ℕ
  | .obstruentStop => 0 | .fricative => 1 | .liquid => 2 | .glide => 3 | .glottal => 4
  | .vowel => 5 | .sonorantStop => 6

instance : LinearOrder NasalCompatibility :=
  LinearOrder.lift' rank fun a b h ↦ by cases a <;> cases b <;> simp_all [rank]

/-- The class of a segment: a glottal if it has none of the places [labial], [coronal] and
[dorsal]; among the other segments that are [−consonantal], a vowel if [+syllabic] and otherwise
a glide; among the rest, a fricative or an obstruent stop if [−sonorant], according to
[continuant], else a sonorant stop if [−approximant], and otherwise a liquid. -/
def ofSegment (s : Segment) : NasalCompatibility :=
  if s .labial = false ∧ s .coronal = false ∧ s .dorsal = false then .glottal
  else if s .consonantal = false then
    if s .syllabic = true then .vowel else .glide
  else if s .sonorant = false then
    if s .continuant = true then .fricative else .obstruentStop
  else if s .approximant = false then .sonorantStop
  else .liquid

/-- The segments that a nasal harmony with cut `c` spreads through: those of class `c` or of a
more compatible class, short of the sonorant stops. -/
def IsTarget (c : NasalCompatibility) (s : Segment) : Prop := ofSegment s ∈ Set.Ico c sonorantStop

instance (c : NasalCompatibility) : DecidablePred c.IsTarget := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

variable {c c' : NasalCompatibility} {s t : Segment}

/-- A segment at least as compatible with nasalization as a target, and not a sonorant stop, is
a target. -/
theorem IsTarget.of_le (h : c.IsTarget s) (hst : ofSegment s ≤ ofSegment t)
    (ht : ofSegment t < sonorantStop) : c.IsTarget t :=
  ⟨h.1.trans hst, ht⟩

/-- A lower cut takes every target of a higher one. -/
theorem IsTarget.anti (h : c'.IsTarget s) (hc : c ≤ c') : c.IsTarget s := ⟨hc.trans h.1, h.2⟩

/-- No segment is a target with the cut at the sonorant stops. -/
theorem not_isTarget_sonorantStop : ¬ sonorantStop.IsTarget s := fun h ↦
  lt_irrefl _ (h.1.trans_lt h.2)

/-- The cut at the glides takes the segments that are [−consonantal] and the glottals. -/
theorem isTarget_glide_iff : glide.IsTarget s ↔
    s .consonantal = false ∨ s .labial = false ∧ s .coronal = false ∧ s .dorsal = false := by
  by_cases hp : s .labial = false ∧ s .coronal = false ∧ s .dorsal = false
  · rw [IsTarget, ofSegment, ite_eq_left hp]
    exact iff_of_true (by decide) (.inr hp)
  · by_cases hc : s .consonantal = false
    · rw [IsTarget, ofSegment, ite_eq_right hp, ite_eq_left hc]
      exact iff_of_true (by split_ifs <;> decide) (.inl hc)
    · rw [IsTarget, ofSegment, ite_eq_right hp, ite_eq_right hc]
      exact iff_of_false (by split_ifs <;> decide) (not_or.2 ⟨hc, hp⟩)

/-- The sonority of a class: the glottals, with the fricatives and the obstruent stops, are
obstruents, and the sonorant stops are the nasals. -/
def toSonority : NasalCompatibility → Sonority
  | .obstruentStop | .fricative | .glottal => .obstruent
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel
  | .sonorantStop => .nasal

/-- On each column of the sonority table, the nasalization class of a segment has that column's
sonority. -/
theorem toSonority_ofSegment_toSegment (c : Sonority) :
    (ofSegment c.toSegment).toSonority = c := by
  cases c <;> decide

/-- Sonority rises with compatibility with nasalization among the classes other than the
glottals and the sonorant stops. -/
theorem monotoneOn_toSonority : MonotoneOn toSonority {glottal, sonorantStop}ᶜ := by decide

/-- Sonority does not rise with compatibility with nasalization among all classes: the sonorant
stops are the most compatible and less sonorous than the liquids. -/
theorem not_monotone_toSonority : ¬ Monotone toSonority := fun h ↦
  absurd (h (by decide : liquid ≤ sonorantStop)) (by decide)

open Data.PHOIBLE.FeatureMatrix in
/-- Chart segments fall into the classes of their glyphs: the glottal stop, which the chart has
[+consonantal], with [h] and [ɦ], and the tap with the liquids. -/
example : [«p», «f», «l», «ɾ», «j», «ʔ», «h», «ɦ», «a», «m»].map
      (ofSegment ∘ Data.PHOIBLE.FeatureMatrix.toSegment) =
    [.obstruentStop, .fricative, .liquid, .liquid, .glide, .glottal, .glottal, .glottal, .vowel,
      .sonorantStop] := by
  decide

end NasalCompatibility

end Phonology
