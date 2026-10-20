module

public import Linglib.Core.Data.Fintype.Order
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Linglib.Phonology.FeatureGeometry
public import Mathlib.Data.List.Iterate
public import Linglib.Phonology.Segmental.FeatureClass
public import Linglib.Phonology.Autosegmental.NonCrossing
public import Linglib.Core.Order.Interval.Basic
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Sagey (1986): the representation of features and relations in non-linear phonology

Sagey's feature geometry has a class node for each independently functioning articulator, the
larynx, the soft palate, the lips, the tongue front and the tongue body, grouped under a
laryngeal and a supralaryngeal node with a place node over the three oral articulators. Each
terminal feature hangs from one class node, and the degree-of-closure features `[continuant]`
and `[consonantal]` hang directly from the root. A class node is present or absent, never minus,
and a terminal feature under an articulator node implies that articulator. Three consequences
follow from the feature classes of the tree: place assimilation leaves degree of closure and
nasality untouched, as in Kpelle and Sanskrit; features of distinct articulators can stand in no
dependency, so the rounding-under-height structure proposed for Yawelmani is unrepresentable;
and a rounded coronal is a complex segment, so a language that admits one articulator under the
place node rounds only labials.

Association lines represent overlap in time rather than simultaneity, which lets a contour
segment share one timing slot and a geminate one melody. Two valid associations cannot cross, so
Goldsmith's well-formedness condition against crossing lines is eliminated: the index-level
No-Crossing Constraint of `Phonology/Autosegmental/NonCrossing` holds of any link set realised by
valid associations.

## Main definitions

* `Node`, `node` — the articulator geometry and the class node of each terminal feature, an
  instance of `Phonology.FeatureGeometry`.
* `Segment.Licensed` — a terminal feature under an articulator node implies that articulator.
* `Association`, `Association.Valid`, `TierRealization` — association lines as overlap in time,
  and two tiers placed in time.

## Main results

* `degreeOfClosure_mem_featureClass_iff`, `nasal_mem_featureClass_iff` — degree of closure lies
  in the root's class alone and nasality in the classes of the soft palate and its ancestors, so
  place assimilation leaves both untouched.
* `disjoint_featureClass_of_articulators` — distinct articulators have disjoint classes.
* `isComplex_of_round_of_coronal`, `occlusions_isComplex` — a licensed rounded coronal and every
  multiple occlusion are complex.
* `Association.Valid.not_crosses`, `isNonCrossing_of_valid` — valid associations do not cross,
  so the No-Crossing Constraint is derived.

## Implementation notes

The substrate's features are mapped onto the dissertation's: `[voice]` stands in for the
laryngeal stiffness and slackness features, `[lateral]` is placed under the supralaryngeal
node, which the Klamath evidence supports without fixing the node below it, and the acoustic
residue `[sonorant]` and `[strident]` together with the features the dissertation lacks are
left unplaced. The major-articulator pointer from the root and the phonetic default degree of
closure of minor articulators are not formalized; the root placement of the degree-of-closure
features that motivates the pointer is.

## References

* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
-/

@[expose] public section

namespace Sagey1986

open Phonology Phonology.FeatureGeometry Autosegmental

/-! ### The articulator geometry -/

/-- The class nodes are the root, the laryngeal and supralaryngeal nodes, the soft palate and
place nodes under the latter, and the articulators labial, coronal and dorsal under place. -/
inductive Node where
  | root
  | laryngeal
  | supralaryngeal
  | softPalate
  | place
  | labial
  | coronal
  | dorsal
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node, the root fixed. -/
def pred : Node → Node
  | .root => .root
  | .laryngeal | .supralaryngeal => .root
  | .softPalate | .place => .supralaryngeal
  | .labial | .coronal | .dorsal => .place

/-- `a ≤ b` when `a` lies on the walk from `b` up to the root, so the root is `⊥` and the parent
is `Order.pred`. -/
instance : PartialOrder Node where
  le a b := a ∈ List.iterate pred b (Fintype.card Node)
  le_refl := by decide
  le_trans := by decide +kernel
  le_antisymm := by decide

instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (a ∈ List.iterate pred b _))

instance : DecidableLT Node := decidableLTOfDecidableLE

instance : OrderBot Node where
  bot := .root
  bot_le := by decide

/-- The parent as the predecessor. -/
instance : PredOrder Node where
  pred := pred
  pred_le := by decide
  min_of_le_pred := by decide
  le_pred_of_lt := by decide

/-- The class feature of an articulator node, present exactly when the articulator is active
in the segment. -/
def feature? : Node → Option Feature
  | .labial => some .labial
  | .coronal => some .coronal
  | .dorsal => some .dorsal
  | _ => none

/-- The articulator nodes under place, whose distinct combinations are the complex segments. -/
def articulators : Finset Node := {.labial, .coronal, .dorsal}

/-- Neither of two distinct articulators dominates the other. -/
theorem not_le_of_mem_articulators {a b : Node} (ha : a ∈ articulators) (hb : b ∈ articulators)
    (hab : a ≠ b) : ¬ a ≤ b := by
  revert a b; decide

end Node

/-- Each terminal feature hangs from a class node. The degree-of-closure features hang from the
root, the glottal features from the laryngeal node, nasality from the soft palate, laterality
from the supralaryngeal node, and the place features from their articulators. -/
def node : Feature → Option Node
  | .continuant | .consonantal => some .root
  | .voice | .spreadGlottis | .constrGlottis => some .laryngeal
  | .nasal => some .softPalate
  | .lateral => some .supralaryngeal
  | .labial | .round => some .labial
  | .coronal | .anterior | .distributed => some .coronal
  | .dorsal | .high | .low | .back => some .dorsal
  | .syllabic | .sonorant | .approximant | .delayedRelease | .strident | .tap | .trill
  | .labiodental | .front | .tense | .atr | .rtr => none

/-! ### Feature classes -/

/-- The degree-of-closure features belong to the root's class alone, so spreading any class node
below the root, as place assimilation does, leaves the degree of closure untouched. -/
theorem degreeOfClosure_mem_featureClass_iff :
    ∀ f ∈ ({.continuant, .consonantal} : Finset Feature), ∀ a : Node,
      f ∈ featureClass node a ↔ a = ⊥ := by
  decide

/-- Nasality is in the classes of the soft palate node and its ancestors alone, so place
assimilation leaves it and spreading the supralaryngeal node carries it, as in Klamath. -/
theorem nasal_mem_featureClass_iff (a : Node) :
    .nasal ∈ featureClass node a ↔ a ≤ .softPalate := by
  revert a; decide

/-- Distinct articulators have disjoint classes, so a feature of one, such as rounding, can depend
on no node of another, such as height. -/
theorem disjoint_featureClass_of_articulators {a b : Node} (ha : a ∈ Node.articulators)
    (hb : b ∈ Node.articulators) (hab : a ≠ b) :
    Disjoint (featureClass node a : Finset Feature) (featureClass node b) :=
  disjoint_featureClass ⟨Node.not_le_of_mem_articulators ha hb hab,
    Node.not_le_of_mem_articulators hb ha hab.symm⟩

/-! ### Complex segments -/

/-- A segment is licensed when every terminal feature it specifies under an articulator node,
whichever its value, activates that articulator. -/
def _root_.Phonology.Segment.Licensed (s : Segment) : Prop :=
  ∀ f, (s f).isSome → ∀ n ∈ node f, ∀ g ∈ n.feature?, s g = some true

instance (s : Segment) : Decidable s.Licensed := by unfold Segment.Licensed; infer_instance

/-- A rounded coronal is complex, since rounding activates the labial articulator; a language
that admits one articulator under the place node therefore rounds only labials. -/
theorem isComplex_of_round_of_coronal {s : Segment} (hs : s.Licensed) (hr : (s .round).isSome)
    (hc : s .coronal = some true) : s.IsComplex := by
  have hl : s .labial = some true := hs .round hr .labial rfl .labial rfl
  exact Finset.one_lt_card.2 ⟨.labial, by simp [Segment.articulators, hl], .coronal,
    by simp [Segment.articulators, hc], by decide⟩

/-- The double occlusions of Halle's survey and the Kinyarwanda triple occlusion are the
labiovelar, labiocoronal, coronovelar and labiocoronovelar stops. -/
def kp : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.labial, true), (.dorsal, true)]

def pt : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.labial, true), (.coronal, true), (.anterior, true)]

def click : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.coronal, true), (.dorsal, true)]

def tkw : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.labial, true), (.round, true), (.coronal, true), (.anterior, true), (.dorsal, true)]

/-- The rounded labial nasal of Aneityum, whose inventory admits one articulator under place. -/
def mw : Segment := Segment.ofSpecs [(.consonantal, true), (.continuant, false),
  (.nasal, true), (.labial, true), (.round, true)]

/-- Every multiple occlusion is complex, and the rounded labial is licensed yet simple. -/
theorem occlusions_isComplex :
    kp.IsComplex ∧ pt.IsComplex ∧ click.IsComplex ∧ tkw.IsComplex ∧
      mw.Licensed ∧ ¬ mw.IsComplex := by
  decide

/-! ### Association lines -/

section Association

variable {T : Type*} [LinearOrder T]

/-- An association line between a timing position and a melodic element, each occupying an
interval of time. -/
structure Association (T : Type*) [LinearOrder T] where
  timing : NonemptyInterval T
  melody : NonemptyInterval T

/-- An association line is valid when some instant of the melody is simultaneous with some
instant of the timing position, so that it represents overlap in time. -/
def Association.Valid (a : Association T) : Prop := a.timing.Overlaps a.melody

instance (a : Association T) : Decidable a.Valid :=
  inferInstanceAs (Decidable (a.timing.Overlaps a.melody))

/-- Two associations cross when their timing positions are ordered one way and their melodies
the other. -/
def Association.Crosses (a b : Association T) : Prop :=
  a.timing.Precedes b.timing ∧ b.melody.Precedes a.melody

/-- Valid associations do not cross, since the two precedences and the two overlaps of a
crossing would chain into an instant preceding itself. -/
theorem Association.Valid.not_crosses {a b : Association T} (ha : a.Valid) (hb : b.Valid) :
    ¬ a.Crosses b := by
  rintro ⟨ht, hm⟩
  exact lt_irrefl _ (((hm.trans_le ha.2).trans ht).trans_le hb.1)

/-- A set of association lines satisfies the No-Crossing Constraint when no two of them
cross. -/
def IsNoCrossing (S : Set (Association T)) : Prop := S.Pairwise fun a b ↦ ¬ a.Crosses b

/-- Any set of valid associations satisfies the No-Crossing Constraint. -/
theorem isNoCrossing_of_forall_valid {S : Set (Association T)} (h : ∀ a ∈ S, a.Valid) :
    IsNoCrossing S :=
  fun _ ha _ hb _ ↦ (h _ ha).not_crosses (h _ hb)

/-- A realisation places two tiers in time, with intervals for the timing positions and for the
melodic elements and each tier's order realised as precedence. -/
structure TierRealization (T : Type*) [LinearOrder T] where
  timing : ℕ → NonemptyInterval T
  melody : ℕ → NonemptyInterval T
  timing_precedes : ∀ {i j : ℕ}, i < j → (timing i).Precedes (timing j)
  melody_precedes : ∀ {k l : ℕ}, k < l → (melody k).Precedes (melody l)

/-- The association realising the link of melodic element `k` to timing position `i`. -/
def TierRealization.assoc (R : TierRealization T) (k i : ℕ) : Association T :=
  ⟨R.timing i, R.melody k⟩

/-- A link set whose links are all realised as valid associations satisfies Goldsmith's
index-level No-Crossing Constraint. -/
theorem isNonCrossing_of_valid (R : TierRealization T) {links : Finset (ℕ × ℕ)}
    (h : ∀ p ∈ links, (R.assoc p.1 p.2).Valid) : IsNonCrossing links := by
  rw [isNonCrossing_iff]
  intro l₁ hl₁ l₂ hl₂ hlt
  by_contra hgt
  push Not at hgt
  exact (h l₂ hl₂).not_crosses (h l₁ hl₁) ⟨R.timing_precedes hgt, R.melody_precedes hlt⟩

/-- Position `n` of either tier occupies the interval from `2n` to `2n + 1`. -/
def TierRealization.canonical : TierRealization ℤ where
  timing n := ⟨⟨2 * n, 2 * n + 1⟩, by omega⟩
  melody n := ⟨⟨2 * n, 2 * n + 1⟩, by omega⟩
  timing_precedes h := by simp only [NonemptyInterval.Precedes]; omega
  melody_precedes h := by simp only [NonemptyInterval.Precedes]; omega

/-- Every diagonal link is valid under the canonical realisation, so the hypothesis of
`isNonCrossing_of_valid` is satisfiable. -/
theorem canonical_diagonal_valid (n : ℕ) : (TierRealization.canonical.assoc n n).Valid := by
  simp only [Association.Valid, TierRealization.canonical, TierRealization.assoc,
    NonemptyInterval.Overlaps]
  omega

end Association

def assoc (ts tf ms mf : ℤ) (ht : ts ≤ tf := by omega) (hm : ms ≤ mf := by omega) :
    Association ℤ :=
  ⟨⟨⟨ts, tf⟩, ht⟩, ⟨⟨ms, mf⟩, hm⟩⟩

/-- A contour segment, two melodies sequenced within one timing slot, and a geminate, one
melody spanning two timing slots, are both pairs of valid associations, which simultaneity
would forbid by identifying the two melodies, or the two slots. -/
theorem contour_geminate_valid :
    ((assoc 0 4 0 2).Valid ∧ (assoc 0 4 2 4).Valid) ∧
      ((assoc 0 1 0 3).Valid ∧ (assoc 2 3 0 3).Valid) := by
  decide

end Sagey1986
