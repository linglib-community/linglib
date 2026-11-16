module

public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.Segmental.Defs
public import Mathlib.Data.Finset.Card

/-!
# Feature classes

Hayes's grouping of the distinctive features into manner, laryngeal and place features, with the
place features split among the three major articulators [labial], [coronal] and [dorsal]. Each
feature has [the class](##Phonology.Feature.featureClass?) it is listed under, and
[the features of a class](##Phonology.FeatureClass.features) are those listed under it or under a
class it contains, so the place class is the union of the three articulator classes. A
[complex segment](##Phonology.Segment.IsComplex) is one with more than one major articulator, and
two segments are [homorganic](##Phonology.Segment.Homorganic) when they agree on the major
articulator features.

## Implementation notes

The class labels are ordered by containment alone, Place above the three articulators, with
manner and laryngeal beside it: a forest with no root, whose feature classes are those of
`Phonology/FeatureGeometry.lean`. Hayes treats Place as a group concept and draws no tree, Padgett
defines feature classes as sets of features, and Halle, Vaux and Wolfe record that there is no
consensus on which revisions of the geometry to adopt. Trees are built in the studies of the works
that argue for them.

[tense], which Hayes's consonant charts print under the place heading but his list of the place
features leaves out, and the tongue-root features [ATR] and [RTR] belong to no class.

## References

* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [J. Padgett, *Feature Classes in Phonology* (2002)][padgett-2002]
* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
-/

@[expose] public section

namespace Phonology

/-- The feature classes: the manner and laryngeal features, headed as such in Hayes's consonant
charts ([hayes-2009] Table 4.7), the place features ([hayes-2009] p. 89), which Padgett's Place
"simply stands for" ([padgett-2002] p. 82), and the place features of each major articulator, the
columns of Hayes's list. -/
inductive FeatureClass where
  | manner | laryngeal | place | labial | coronal | dorsal
  deriving DecidableEq, Repr, Fintype

namespace FeatureClass

/-- `a ≤ b` when class `a` contains class `b`: the place class contains the three articulator
classes. -/
instance : PartialOrder FeatureClass where
  le a b := a = b ∨ a = place ∧ (b = labial ∨ b = coronal ∨ b = dorsal)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE FeatureClass := fun a b ↦
  inferInstanceAs (Decidable (a = b ∨ a = place ∧ (b = labial ∨ b = coronal ∨ b = dorsal)))

/-- No class lies in two classes neither of which contains the other. -/
instance : IsLeftLinear FeatureClass := ⟨by decide⟩

end FeatureClass

/-- The class of a feature, with [syllabic] a manner feature by the sonority hierarchy
([hayes-2009] §4.4.1), and none for [tense], [ATR] and [RTR]. -/
def Feature.featureClass? : Feature → Option FeatureClass
  | .syllabic | .consonantal | .sonorant | .approximant | .continuant | .delayedRelease
  | .nasal | .tap | .trill => some .manner
  | .voice | .spreadGlottis | .constrGlottis => some .laryngeal
  | .labial | .round | .labiodental => some .labial
  | .coronal | .anterior | .distributed | .strident | .lateral => some .coronal
  | .dorsal | .high | .low | .front | .back => some .dorsal
  | .tense | .atr | .rtr => none

namespace FeatureClass

/-- The features of a class, those listed under it or under a class it contains. -/
def features (c : FeatureClass) : Finset Feature :=
  FeatureGeometry.featureClass Feature.featureClass? c

/-- The place features are those of the three major articulators. -/
theorem features_place : place.features = labial.features ∪ coronal.features ∪ dorsal.features := by
  decide

end FeatureClass

/-! ### Major articulators -/

/-- The major articulator features [labial], [coronal] and [dorsal] ([hayes-2009] §4.6.1). -/
def Feature.majorArticulators : Finset Feature := {.labial, .coronal, .dorsal}

@[simp] theorem Feature.mem_majorArticulators {f : Feature} :
    f ∈ Feature.majorArticulators ↔ f = .labial ∨ f = .coronal ∨ f = .dorsal := by
  simp [Feature.majorArticulators]

/-- The major articulators of a segment, the major articulator features it is specified `+` for:
Halle, Vaux and Wolfe's designated articulators ([halle-vaux-wolfe-2000] §1.2.2). -/
def Segment.articulators (s : Segment) : Finset Feature :=
  Feature.majorArticulators.filter (s.HasValue · true)

/-- Two segments are homorganic when they agree on the major articulator features. -/
def Segment.Homorganic (s t : Segment) : Prop := Set.EqOn s t ↑Feature.majorArticulators

instance : DecidableRel Segment.Homorganic := fun s t ↦
  inferInstanceAs (Decidable (∀ f ∈ Feature.majorArticulators, s f = t f))

/-! ### Complex segments -/

/-- A complex segment has more than one major articulator, as the labial-velars are [+labial,
+dorsal] and the palatals [+coronal, +dorsal] ([hayes-2009] p. 84, Table 4.8). Whether [kʷ] is
complex depends on its representation: labialization adds [+labial, +round] for Hayes
([hayes-2009] p. 86), and leaves [labial] unspecified for Halle, Vaux and Wolfe
([halle-vaux-wolfe-2000] p. 435). -/
def Segment.IsComplex (s : Segment) : Prop := 1 < s.articulators.card

instance : DecidablePred Segment.IsComplex := fun _ ↦ inferInstanceAs (Decidable (1 < _))

end Phonology
