module

public import Linglib.Phonology.Segmental.Defs
public import Linglib.Core.Order.Laminar
public import Mathlib.Data.Finset.Card

/-!
# Feature classes

Hayes's grouping of the distinctive features into manner, laryngeal and place features, with the
place features split among the three major articulators [labial], [coronal] and [dorsal]. The
classes are finite sets of features, [the features](##Phonology.FeatureClass.features) listed
under each of five labels, and [the place class](##Phonology.FeatureClass.place) is the union of
the three articulator classes. [No two of them overlap](##Phonology.FeatureClass.isLaminar) unless
one contains the other. A [complex segment](##Phonology.Segment.IsComplex) is one with more than
one major articulator, and two segments are [homorganic](##Phonology.Segment.Homorganic) when they
agree on the major articulator features.

## Implementation notes

The classes are sets rather than the nodes of a tree. Hayes treats Place as a group concept and
draws no tree, Padgett defines feature classes as sets of features, and Halle, Vaux and Wolfe
record that there is no consensus on which revisions of the geometry to adopt. Trees are built
on `Phonology/FeatureGeometry.lean` in the studies of the works that argue for them.

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

/-- The classes do not overlap: the five listed classes are pairwise disjoint and the place class
contains three of them. -/
theorem isLaminar : IsLaminar (insert place (Set.range features)) := by
  have h : ∀ c d : FeatureClass, c.features ⊆ d.features ∨ d.features ⊆ c.features ∨
      Disjoint c.features d.features := by decide
  have hp : ∀ c : FeatureClass, c.features ⊆ place ∨ Disjoint c.features place := by decide
  rintro _ (rfl | ⟨c, rfl⟩) _ (rfl | ⟨d, rfl⟩)
  · exact .inl le_rfl
  · exact (hp d).elim (fun h ↦ .inr (.inl h)) fun h ↦ .inr (.inr h.symm)
  · exact (hp c).elim .inl fun h ↦ .inr (.inr h)
  · exact h c d

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
