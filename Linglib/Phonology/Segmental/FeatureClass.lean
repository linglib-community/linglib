module

public import Linglib.Phonology.Segmental.Defs
public import Mathlib.Data.Finset.Card

/-!
# Feature classes

Hayes's grouping of the distinctive features into manner, laryngeal and place features, with the
place features split among the three major articulators [labial], [coronal] and [dorsal]. The
classes are finite sets of features, the place class is their union, and a complex segment is one
with more than one major articulator.

## Main definitions

* `FeatureClass`, `Feature.featureClass?`: the five classes and the class of each feature.
* `FeatureClass.features`, `FeatureClass.place`: the features of a class, and the place class.
* `Segment.articulators`, `Segment.IsComplex`: the major articulators of a segment, and complex
  segments.

## Implementation notes

The classes are sets rather than the nodes of a tree. Hayes treats Place as a group concept and
draws no tree, Padgett defines feature classes as sets of features, and Halle, Vaux and Wolfe
record that there is no consensus on which revisions of the geometry to adopt. Trees are instances
of `Phonology/FeatureGeometry.lean` in the studies of the works that argue for them.

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
charts ([hayes-2009] Table 4.7), and the place features of each major articulator, the columns of
his list of the place features ([hayes-2009] p. 89). -/
inductive FeatureClass where
  | manner | laryngeal | labial | coronal | dorsal
  deriving DecidableEq, Repr, Fintype

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

/-- The features of a class. -/
def features (c : FeatureClass) : Finset Feature := Finset.univ.filter (·.featureClass? = some c)

/-- The place class, the union of the three articulator classes: Hayes's place features
([hayes-2009] p. 89), and Padgett's Place, which "simply stands for the set {[labial],
[coronal], [dorsal], …}" ([padgett-2002] p. 82). -/
def place : Finset Feature := labial.features ∪ coronal.features ∪ dorsal.features

variable {f : Feature} {c : FeatureClass}

@[simp] theorem mem_features : f ∈ c.features ↔ f.featureClass? = some c := by simp [features]

theorem mem_place :
    f ∈ place ↔ f.featureClass? = some .labial ∨ f.featureClass? = some .coronal ∨
      f.featureClass? = some .dorsal := by
  simp [place]

end FeatureClass

/-! ### Complex segments -/

/-- The major articulators of a segment, the major articulator features ([hayes-2009] §4.6.1) it
is specified `+` for: Halle, Vaux and Wolfe's designated articulators ([halle-vaux-wolfe-2000]
§1.2.2). -/
def Segment.articulators (s : Segment) : Finset Feature :=
  ({.labial, .coronal, .dorsal} : Finset Feature).filter (s.HasValue · true)

/-- A complex segment has more than one major articulator, as the labial-velars are [+labial,
+dorsal] and the palatals [+coronal, +dorsal] ([hayes-2009] p. 84, Table 4.8). Whether [kʷ] is
complex depends on its representation: labialization adds [+labial, +round] for Hayes
([hayes-2009] p. 86), and leaves [labial] unspecified for Halle, Vaux and Wolfe
([halle-vaux-wolfe-2000] p. 435). -/
def Segment.IsComplex (s : Segment) : Prop := 1 < s.articulators.card

instance : DecidablePred Segment.IsComplex := fun _ ↦ inferInstanceAs (Decidable (1 < _))

end Phonology
