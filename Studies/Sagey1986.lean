module

public import Linglib.Core.Order.SuccPred.Tree
public import Linglib.Phonology.Autosegmental.IntervalOrder
public import Linglib.Phonology.Autosegmental.TwoTier
public import Linglib.Phonology.Segmental.FeatureClass
public import Studies.Clements1985

/-!
# Sagey (1986): the representation of features and relations in non-linear phonology

The feature geometry of Sagey's dissertation has a class node for each independently functioning
articulator: the larynx, the soft palate, the lips, the tongue front and the tongue body. A
laryngeal and a supralaryngeal node hang from the root, a soft palate and a place node from the
supralaryngeal node, and the labial, coronal and dorsal nodes from the place node. Each terminal
feature hangs from one class node, the degree-of-closure features `[continuant]` and
`[consonantal]` from the root. The tree is an instance of `Phonology/FeatureGeometry.lean`, and
spreading a class node gives the target the trigger's values for the features of its class. So
place assimilation leaves the degree of closure, the nasality and the laryngeal features of its
target (`spread_place`), and distinct articulators have disjoint classes
(`disjoint_featureClass_of_articulators`), so that no feature of one depends on a feature of
another.

A segment bears a class node when it specifies a feature at or below it, so a node is present
or absent and has no minus value, and a terminal feature under an articulator node, whichever its
value, brings that node with it. The articulators of a segment are the articulator nodes it
bears, and a complex segment has more than one. So the articulators of a complex segment are one
of the three pairs or the triple (`isComplex_iff`), a segment specified for `[round]` that has
one articulator has the labial one (`articulators_eq_labial_of_round`), and place assimilation
gives its target the articulators of its trigger, complex or not (`articulators_spread_place`).

An association line joins positions of two tiers. A reading sends the positions to events
ordered by a precedence, `Autosegmental.AR.IsReading`, the order of each tier going to the
precedence. A line may then be read as simultaneity, its two positions at one event, or, with
intervals for events, as overlap, the two sharing an instant. Under simultaneity the lines
between two tiers pair their positions one to one and in order (`lt_iff_lt_of_isReading_eq`),
which excludes the contour segment, the geminate and the discontinuous link. Under overlap,
`Autosegmental.AR.HasIntervalOrder`, all three can be placed, and by
`Autosegmental.AR.HasIntervalOrder.noCrossing` a representation that can be placed has no
crossing lines, so that the No-Crossing Constraint is not a separate condition.

## Implementation notes

The features `[labial]`, `[coronal]` and `[dorsal]` of the substrate's segments hang from the
articulator nodes and stand for a node with no terminal feature under it; the segments here have
them only as `+`. `IsComplex` counts the articulator nodes a segment bears, where the substrate's
`Phonology.Segment.IsComplex` counts the major articulator features it has `+`, and the two
differ on a rounded segment with no `[labial]`.

`[voice]` stands in for the laryngeal features of stiffness and slackness. `[lateral]` is placed
at the supralaryngeal node, under which the Klamath evidence puts it; whether it hangs from that
node or from the place node is left open. `[sonorant]` and `[strident]`, which the dissertation
sets aside as acoustic, and the features it lacks are unplaced. The segments are specified as
the dissertation draws them, for the nodes and features under discussion and nothing else.

Spreading a node delinks the target's own values under it. The geometry keeps the root,
laryngeal, supralaryngeal and place nodes of `Studies/Clements1985.lean` and has no manner node.

## TODO

* The major articulator of a segment, the articulator to which the degree-of-closure features at
  the root apply, is a pointer from the root to an articulator node, carried only when the root
  spreads; minor articulators take a predictable degree of closure. Segments here have no
  pointer.
* Contour segments branch for terminal features only, never for class nodes.
* Goldsmith's formal well-formedness condition, stated on an ordered sequence of lines, admits
  crossing lines between tiers of two elements; the comparison is not formalized.

## References

* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
-/

@[expose] public section

namespace Sagey1986

open Phonology Phonology.FeatureGeometry Autosegmental

/-! ### The articulator geometry -/

/-- (4): the class nodes are the root, the laryngeal and supralaryngeal nodes, the soft palate
and place nodes under the latter, and the articulators labial, coronal and dorsal under place. -/
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

/-- (4): the tree of class nodes. -/
def tree : ParentTree Node := .ofIterate pred .root 3 (by decide)

/-- `a ≤ b` when `a` dominates `b`, so the root is `⊥` and the parent is `Order.pred`. -/
instance : PartialOrder Node := tree.toPartialOrder

instance : DecidableLE Node := tree.decidableLE

instance : DecidableLT Node := decidableLTOfDecidableLE

instance : OrderBot Node := tree.toOrderBot

instance : PredOrder Node := tree.toPredOrder

/-- The articulator nodes under place. -/
def articulators : Finset Node := {.labial, .coronal, .dorsal}

theorem not_le_of_mem_articulators {a b : Node} (ha : a ∈ articulators) (hb : b ∈ articulators)
    (hab : a ≠ b) : ¬ a ≤ b := by
  revert a b; decide

theorem place_le_of_mem_articulators {a : Node} (ha : a ∈ articulators) : place ≤ a := by
  revert a; decide

end Node

/-- (4): the class node each terminal feature hangs from. The degree-of-closure features hang
from the root, the glottal features from the laryngeal node, nasality from the soft palate,
laterality from the supralaryngeal node, and the place features from their articulators. -/
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

theorem degreeOfClosure_mem_featureClass_iff :
    ∀ f ∈ ({.continuant, .consonantal} : Finset Feature), ∀ a : Node,
      f ∈ featureClass node a ↔ a = ⊥ := by
  decide

theorem nasal_mem_featureClass_iff (a : Node) :
    .nasal ∈ featureClass node a ↔ a ≤ .softPalate := by
  revert a; decide

/-- Distinct articulators have disjoint classes, so a feature of one, such as rounding, depends
on no node of another, such as height. -/
theorem disjoint_featureClass_of_articulators {a b : Node} (ha : a ∈ Node.articulators)
    (hb : b ∈ Node.articulators) (hab : a ≠ b) :
    Disjoint (featureClass node a : Finset Feature) (featureClass node b) :=
  disjoint_featureClass ⟨Node.not_le_of_mem_articulators ha hb hab,
    Node.not_le_of_mem_articulators hb ha hab.symm⟩

theorem featureClass_place_clements_subset :
    featureClass Clements1985.classNode? .place ⊆ featureClass node .place := by
  decide

/-! ### Articulators -/

/-- The articulators of a segment are the articulator nodes it bears. -/
def articulators (s : Segment) : Finset Node := Node.articulators.filter (Bears node ⇑s)

/-- A complex segment has more than one articulator under its place node. -/
def IsComplex (s : Segment) : Prop := 1 < (articulators s).card

instance : DecidablePred IsComplex := fun _ ↦ inferInstanceAs (Decidable (1 < _))

variable {s : Segment}

/-- A segment specified for rounding that has a single articulator has the labial one. -/
theorem articulators_eq_labial_of_round (hr : (s .round).isSome) (h : ¬ IsComplex s) :
    articulators s = {.labial} :=
  have hl : .labial ∈ articulators s :=
    Finset.mem_filter.2 ⟨by decide, bears_of_isSome (f := .round) rfl hr le_rfl⟩
  Finset.eq_singleton_iff_unique_mem.2
    ⟨hl, fun _ hx ↦ Finset.card_le_one.1 (not_lt.1 h) _ hx _ hl⟩

-- (2)
theorem isComplex_iff : IsComplex s ↔ articulators s ∈
    ({{.labial, .coronal}, {.labial, .dorsal}, {.coronal, .dorsal},
      {.labial, .coronal, .dorsal}} : Finset (Finset Node)) := by
  have h : ∀ a b c : Bool,
      let t := Node.articulators.filter fun g ↦
        (g = .labial ∧ a) ∨ (g = .coronal ∧ b) ∨ (g = .dorsal ∧ c)
      1 < t.card ↔ t ∈ ({{.labial, .coronal}, {.labial, .dorsal}, {.coronal, .dorsal},
        {.labial, .coronal, .dorsal}} : Finset (Finset Node)) := by
    decide
  have ht : articulators s = Node.articulators.filter fun g ↦
      (g = .labial ∧ decide (Bears node ⇑s .labial)) ∨
        (g = .coronal ∧ decide (Bears node ⇑s .coronal)) ∨
          (g = .dorsal ∧ decide (Bears node ⇑s .dorsal)) :=
    Finset.filter_congr fun g hg ↦ by
      have hg' : g = .labial ∨ g = .coronal ∨ g = .dorsal := by
        simpa [Node.articulators] using hg
      rcases hg' with rfl | rfl | rfl <;> simp
  unfold IsComplex
  rw [ht]
  exact h _ _ _

/-- (5): the labiovelar stop, a labial and a dorsal node under one place node. -/
def kp : Segment := [−continuant, +labial, +dorsal]

/-- (2): the labiocoronal stop. -/
def pt : Segment := [−continuant, +labial, +coronal]

/-- (2): a click, coronal and dorsal. -/
def click : Segment := [−continuant, +coronal, +dorsal]

/-- (65): the labiovelarized coronal stop of Kinyarwanda. -/
def tkw : Segment := [−continuant, +coronal, +round, +back]

/-- (14a): the rounded labial nasal of Aneityum. -/
def mw : Segment := [−continuant, +nasal, +labial, +round]

/-- (25b): `h`, with a laryngeal node and no supralaryngeal node. -/
def glottal : Segment := [+spreadGlottis]

/-- (14d): the rounded `h` of Nenema, whose only articulator comes with its rounding. -/
def hw : Segment := [+spreadGlottis, +round]

-- (2), (5), (65)
theorem articulators_occlusions :
    articulators kp = {.labial, .dorsal} ∧ articulators pt = {.labial, .coronal} ∧
      articulators click = {.coronal, .dorsal} ∧
        articulators tkw = {.labial, .coronal, .dorsal} := by
  decide

-- (13)
theorem articulators_anterior :
    articulators [+anterior] = {.coronal} ∧ articulators [−anterior] = {.coronal} := by
  decide

-- (14a), (14d), (25b)
theorem articulators_mw_glottal_hw :
    articulators mw = {.labial} ∧ articulators glottal = ∅ ∧
      ¬ Bears node ⇑glottal .supralaryngeal ∧ articulators hw = {.labial} := by
  decide

-- (14)
theorem isComplex_round : IsComplex [+coronal, +round] ∧ IsComplex [+dorsal, +round] := by
  decide

/-! ### Spreading -/

variable (src tgt : Segment)

/-- Place assimilation gives the target the trigger's place features and leaves its degree of
closure, its nasality and its laryngeal features. -/
theorem spread_place :
    Set.EqOn (Segment.spread node .place src tgt) src ↑(featureClass node .place) ∧
      Set.EqOn (Segment.spread node .place src tgt) tgt
        ↑({.continuant, .consonantal} ∪ featureClass node .softPalate ∪
          featureClass node .laryngeal : Finset Feature) :=
  ⟨spread_eqOn, Finset.eqOn_piecewise_of_disjoint (by decide)⟩

/-- Place assimilation gives the target the articulators of the trigger, all of them when the
trigger is complex. -/
theorem articulators_spread_place :
    articulators (Segment.spread node .place src tgt) = articulators src :=
  Finset.filter_congr fun _ hb ↦ bears_spread_of_le (Node.place_le_of_mem_articulators hb)

-- (30), (31a)
theorem spread_supralaryngeal :
    Set.EqOn (Segment.spread node .supralaryngeal src tgt) src
        ↑({.nasal, .lateral} : Finset Feature) ∧
      Set.EqOn (Segment.spread node .supralaryngeal src tgt) tgt
        ↑(featureClass node .laryngeal) :=
  ⟨Finset.eqOn_piecewise_of_subset (by decide),
    spread_eqOn_of_incompRel ⟨by decide, by decide⟩⟩

/-- The prefix nasal of Kpelle, with no place of its own. -/
def nasalStop : Segment := [−continuant, +nasal]

/-- A labial fricative. -/
def labialFricative : Segment := [+continuant, +labial]

/-- A labial stop. -/
def labialStop : Segment := [−continuant, +labial]

/-- An alveolar fricative. -/
def alveolarFricative : Segment := [+continuant, +anterior]

-- (19)
theorem spread_place_labialFricative_nasalStop :
    Segment.spread node .place labialFricative nasalStop = [−continuant, +nasal, +labial] := by
  decide

-- (19)
theorem spread_place_kp_nasalStop :
    Segment.spread node .place kp nasalStop = [−continuant, +nasal, +labial, +dorsal] := by
  decide

-- (22)
theorem spread_place_labialStop_alveolarFricative :
    Segment.spread node .place labialStop alveolarFricative = [+continuant, +labial] := by
  decide

/-- (123): the Fanti trill. -/
def trill : Segment := [−anterior, −distributed]

/-- (123): a high back rounded vowel. -/
def highBackRound : Segment := [+round, +back, +high]

-- (123)
theorem spread_dorsal_highBackRound_trill :
    Segment.spread node .dorsal highBackRound trill =
      [−anterior, −distributed, +back, +high] ∧
    articulators (Segment.spread node .dorsal highBackRound trill) = {.coronal, .dorsal} := by
  decide

/-! ### Association lines -/

section Association

variable {ι E : Type*} {τ : ι → Type*} {X : AR τ} {prec : E → E → Prop} {I : X.Pos → E}

private theorem lt_of_lt [IsStrictOrder E prec] (h : X.IsReading prec Eq I) {i j : ι}
    {p q p' q' : ℕ} (h₁ : X.Link i j p q) (h₂ : X.Link i j p' q') (hlt : p < p') : q < q' := by
  have hq := h.prec_of_lt i (show (⟨p, h₁.lt_left⟩ : Fin _) < ⟨p', h₂.lt_left⟩ from hlt)
  rw [h.ov_of_adj h₁.adj, h.ov_of_adj h₂.adj] at hq
  by_contra! hge
  obtain rfl | hlt' := hge.eq_or_lt
  · exact irrefl_of prec _ hq
  · exact irrefl_of prec _ (trans_of prec hq
      (h.prec_of_lt j (show (⟨q', h₂.lt_right⟩ : Fin _) < ⟨q, h₁.lt_right⟩ from hlt')))

/-- Read as simultaneity, the two positions of a line at one event, the lines between two tiers
pair their positions one to one and in order. -/
theorem lt_iff_lt_of_isReading_eq [IsStrictOrder E prec] (h : X.IsReading prec Eq I) {i j : ι}
    {p q p' q' : ℕ} (h₁ : X.Link i j p q) (h₂ : X.Link i j p' q') : p < p' ↔ q < q' :=
  ⟨lt_of_lt h h₁ h₂, lt_of_lt h h₁.symm h₂.symm⟩

theorem hasIntervalOrder_of_isReading_eq {T : Type*} [LinearOrder T]
    {I : X.Pos → NonemptyInterval T} (h : X.IsReading NonemptyInterval.Precedes Eq I) :
    X.HasIntervalOrder :=
  (h.mono fun a _ hab ↦ by rw [← hab]; exact NonemptyInterval.overlaps_refl a).hasIntervalOrder

end Association

/-- (7a): a contour segment, two values of one feature on one timing slot. -/
abbrev contour : AR (TwoTier Bool Unit) := AR.ofLines [false, true] [()] {(0, 0), (1, 0)}

/-- (7b): a geminate, one feature on two timing slots. -/
abbrev geminate : AR (TwoTier Bool Unit) := AR.ofLines [true] [(), ()] {(0, 0), (0, 1)}

/-- (20): a discontinuous link, one feature on the first and third of three timing slots. -/
abbrev discontinuous : AR (TwoTier Bool Unit) :=
  AR.ofLines [true] [(), (), ()] {(0, 0), (0, 2)}

/-- (23): two features on two timing slots with their lines crossed. -/
abbrev crossing : AR (TwoTier Bool Unit) :=
  AR.ofLines [false, true] [(), ()] {(0, 1), (1, 0)}

-- (9), (10), (13)
theorem not_isReading_eq {E : Type*} (prec : E → E → Prop) [IsStrictOrder E prec] :
    (∀ I, ¬ contour.IsReading prec Eq I) ∧ (∀ I, ¬ geminate.IsReading prec Eq I) ∧
      ∀ I, ¬ discontinuous.IsReading prec Eq I :=
  ⟨fun _ h ↦ absurd ((lt_iff_lt_of_isReading_eq h (i := .upper) (j := .lower) (p := 0) (q := 0)
      (p' := 1) (q' := 0) (by decide) (by decide)).1 (by decide)) (by decide),
    fun _ h ↦ absurd ((lt_iff_lt_of_isReading_eq h (i := .upper) (j := .lower) (p := 0) (q := 0)
      (p' := 0) (q' := 1) (by decide) (by decide)).2 (by decide)) (by decide),
    fun _ h ↦ absurd ((lt_iff_lt_of_isReading_eq h (i := .upper) (j := .lower) (p := 0) (q := 0)
      (p' := 0) (q' := 2) (by decide) (by decide)).2 (by decide)) (by decide)⟩

-- (18), (21)
theorem hasIntervalOrder_contour_geminate_discontinuous :
    contour.HasIntervalOrder ∧ geminate.HasIntervalOrder ∧ discontinuous.HasIntervalOrder :=
  ⟨(AR.noCrossing_iff_hasIntervalOrder_of_card_le_two (by simp)).1 (by decide),
    (AR.noCrossing_iff_hasIntervalOrder_of_card_le_two (by simp)).1 (by decide),
    (AR.noCrossing_iff_hasIntervalOrder_of_card_le_two (by simp)).1 (by decide)⟩

-- (23)
theorem not_hasIntervalOrder_crossing : ¬ crossing.HasIntervalOrder :=
  fun h ↦ absurd h.noCrossing (by decide)

end Sagey1986
