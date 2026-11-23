module

public import Linglib.Core.Order.SuccPred.Tree
public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.Segmental.FeatureClass
public import Linglib.Data.Examples.HalleVauxWolfe2000

/-!
# Halle, Vaux and Wolfe (2000): feature spreading and the representation of place

Halle, Vaux and Wolfe review the four innovations proposed since Clements's feature geometry,
Unified Feature Theory, Vowel-Place Theory, Strict Locality and Partial Spreading, record that no
consensus exists on which to adopt (section 1.1), and keep only Partial Spreading in their Revised
Articulator Theory. Its tree (1) groups the features of the six articulators under the nodes
Lips, Tongue Blade, Tongue Body, Soft Palate, Tongue Root and Larynx, with Place over the three
oral articulators and Guttural over Tongue Root and Larynx, and puts the articulator-free features
[continuant], [strident], [lateral] and [suction] at the root beside the root features
[consonantal] and [sonorant]. So an articulator-free feature lies in the root's class and no
other, Soft Palate is not under Place, and Place is exactly the three oral articulators.
Designated articulators are unary terminal features rather than nodes (section 1.2.2), so the
labiovelar [k͡p] of (4) carries both [labial] and [dorsal] while the labialised [kʷ] carries
[dorsal] beside [+round], and only the first is a complex segment. Spreading operates on terminal
features (section 1.2.3): a rule spreading more than one feature targets the set a node
exhaustively dominates and spreads each feature on its own tier, so blocking one does not stop
the rest. Irish Nasal Place Assimilation spreads the Place class, carrying each oral
articulator's class and leaving the sister Soft Palate alone, and Dorsal Assimilation (44)
spreads the terminal [dorsal] alone, leaving the target's [back] untouched, where spreading the
Tongue Body node would carry it, the prediction (45) of a Place-node analysis that the data
refute (section 2.2.4).

## Main definitions

* `Node`, `node` — tree (1) and the class node of each feature of Hayes's inventory, an instance
  of `Phonology.FeatureGeometry`.
* `kp`, `kw` — the labiovelar and the labialised velar stop of (4).
* `placeAssimilation`, `dorsalAssimilation` — Irish Nasal Place Assimilation and Dorsal
  Assimilation (44).

## Implementation notes

Features of Hayes's inventory absent from (1) are placed by the paper's own articulator-bound
or free criterion (section 1.2): [approximant], [delayed release], [tap], [trill], and [syllabic]
are articulator-free and go to the root, [labiodental] to Lips, [front] to Tongue Body, and
[voice], executed by the larynx, to Larynx; [tense] is left unplaced, since the paper's
tongue-root features are [ATR] and [RTR] and Hayes's [tense] is not identified with them;
[ATR] and [RTR] go to Tongue Root. [suction], [rhinal], [radical], [stiff vocal folds],
[slack vocal folds], and [glottal] have no counterpart in the inventory.

The Irish forms are the rows of `Data.Examples.HalleVauxWolfe2000`.

## TODO

* Section 2's arguments against Unified Feature Theory and Vowel-Place Theory, section 3's
  analyses (Barra Gaelic vowel copy, Irish nasal place and dorsal assimilation), and section
  1.2.4's full specification.

## References

* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

@[expose] public section

namespace HalleVauxWolfe2000

open Phonology Phonology.FeatureGeometry

/-! ### Tree (1) -/

/-- The nodes of tree (1) are the root, Place over Lips, Tongue Blade and Tongue Body, Soft Palate,
and Guttural over Tongue Root and Larynx. -/
inductive Node where
  | root | place | lips | tongueBlade | tongueBody | softPalate | guttural | tongueRoot | larynx
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node, the root fixed. -/
def pred : Node → Node
  | .root => .root
  | .place | .softPalate | .guttural => .root
  | .lips | .tongueBlade | .tongueBody => .place
  | .tongueRoot | .larynx => .guttural

/-- The tree (1). -/
def tree : ParentTree Node := .ofIterate pred .root 2 (by decide)

/-- `a ≤ b` when `a` dominates `b`, so the root is `⊥` and the parent is `Order.pred`. -/
instance : PartialOrder Node := tree.toPartialOrder

instance : DecidableLE Node := tree.decidableLE

instance : DecidableLT Node := decidableLTOfDecidableLE

instance : OrderBot Node := tree.toOrderBot

instance : PredOrder Node := tree.toPredOrder

end Node

/-- The terminal features of (1), read over Hayes's inventory (see the module
docstring for the features the paper does not list). -/
def node : Feature → Option Node
  | .consonantal | .sonorant | .continuant | .strident | .lateral
  | .syllabic | .approximant | .delayedRelease | .tap | .trill => some .root
  | .labial | .round | .labiodental => some .lips
  | .coronal | .anterior | .distributed => some .tongueBlade
  | .dorsal | .high | .low | .back | .front => some .tongueBody
  | .nasal => some .softPalate
  | .voice | .spreadGlottis | .constrGlottis => some .larynx
  | .atr | .rtr => some .tongueRoot
  | .tense => none

/-! ### Articulator-free features and Place -/

/-- The articulator-free features and the root features belong to the root's class alone, since no
articulator node dominates them. -/
theorem articulatorFree_mem_featureClass_iff :
    ∀ f ∈ ({.consonantal, .sonorant, .continuant, .strident, .lateral} : Finset Feature),
      ∀ a : Node, f ∈ featureClass node a ↔ a = ⊥ := by
  decide

/-- Soft Palate is a sister of Place, not under it. -/
theorem nasal_notMem_place : Feature.nasal ∉ featureClass node Node.place := by decide

/-- Place dominates exactly the three oral articulators. -/
theorem place_eq_union :
    featureClass node Node.place =
      featureClass node Node.lips ∪ featureClass node Node.tongueBlade ∪
        featureClass node Node.tongueBody := by
  decide

/-! ### Designated articulators (p. 435) -/

/-- The labiovelar stop is `[dorsal, labial, +consonantal, −sonorant, −round, −continuant]`. -/
def kp : Segment :=
  [+dorsal, +labial, +consonantal, −sonorant, −round, −continuant]

/-- The labialised velar stop is `[dorsal, +consonantal, −sonorant, +round, −continuant]`, with no
specification for [labial]. -/
def kw : Segment :=
  [+dorsal, +consonantal, −sonorant, +round, −continuant]

/-- Only the labiovelar is a complex segment. -/
theorem isComplex_kp : kp.IsComplex := by decide

theorem not_isComplex_kw : ¬ kw.IsComplex := by decide

-- section 1.2.2
theorem bears_lips_kw : Bears node ⇑kw .lips ∧ kw .labial = none := by decide

/-! ### Terminal spreading, sections 1.2.3 and 2.2.4 -/

variable (src tgt : Segment)

/-- Irish Nasal Place Assimilation spreads the terminal features under Place from `src` onto
`tgt`. -/
def placeAssimilation : Segment := Segment.spread node .place src tgt

/-- Spreading Place carries the whole Tongue Body class, which Place contains; in the same way
the Lips and Tongue Blade classes. -/
theorem placeAssimilation_eqOn_tongueBody :
    Set.EqOn (placeAssimilation src tgt) src ↑(featureClass node Node.tongueBody) :=
  spread_eqOn_of_le (by decide)

/-- Soft Palate is a sister of Place, so Place assimilation leaves [nasal] where it was and the
assimilated nasal is still a nasal, the two classes being disjoint. -/
theorem placeAssimilation_nasal : placeAssimilation src tgt .nasal = tgt .nasal :=
  spread_eqOn_of_incompRel (src := ⇑src) (tgt := ⇑tgt) (a := Node.place) (b := Node.softPalate)
    ⟨by decide, by decide⟩ (by decide : Feature.nasal ∈ featureClass node Node.softPalate)

/-- Irish Dorsal Assimilation (44) spreads the designated articulator alone, the terminal
feature [dorsal] rather than the Tongue Body node. -/
def dorsalAssimilation : Segment := Segment.piecewise {Feature.dorsal} src tgt

/-- Spreading terminal [dorsal] leaves the target's [back] untouched (44), so the nasals of (44a)
and (44b) keep their secondary articulation. -/
theorem dorsalAssimilation_back : dorsalAssimilation src tgt .back = tgt .back :=
  Finset.piecewise_eq_of_notMem {Feature.dorsal} src.val tgt.val
    (by decide : Feature.back ∉ ({Feature.dorsal} : Finset Feature))

/-- Spreading the Tongue Body node instead would carry [back] along with [dorsal] (45), the
prediction of a Place-node analysis of (44) that the data refute. -/
theorem tongueBody_spread_back :
    Segment.spread node .tongueBody src tgt .back = src .back :=
  spread_of_mem (node := node) (a := Node.tongueBody) (src := ⇑src) (tgt := ⇑tgt) (by decide)

end HalleVauxWolfe2000
