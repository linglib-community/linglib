module

public import Linglib.Core.Data.Fintype.Order
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Iterate
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

An articulator node is present in a segment or absent from it and has no minus value, and a
terminal feature under an articulator node, whichever its value, implies that node. A segment is
licensed when it meets the second condition, from which the first follows
(`Licensed.ne_some_false`). A complex segment has more than one articulator under its place node,
so its articulators are one of the three pairs or the triple (`isComplex_iff`), and a licensed
segment that is specified for `[round]` and has one articulator has the labial one
(`articulators_eq_labial_of_round`): a language that admits one articulator under the place node
rounds its labials and its placeless segments only.

An association line joins positions of two tiers. With the positions placed in time as intervals
and the order of each tier read as precedence, a line may be read as total simultaneity, the two
intervals being equal, or as overlap, the two sharing an instant. Under simultaneity the lines
between two tiers pair their positions one to one and in order
(`HasSimultaneity.lt_iff_lt`), which excludes the contour segment, the geminate and the
discontinuous link. Under overlap, `Autosegmental.AR.HasIntervalOrder`, all three can be placed,
and by `Autosegmental.AR.HasIntervalOrder.noCrossing` a representation that can be placed has no
crossing lines, so that the No-Crossing Constraint is not a separate condition.

## Implementation notes

The features `[labial]`, `[coronal]` and `[dorsal]` of the substrate's segments stand for the
articulator nodes: a node is present when its feature is `+`, and licensing excludes `−`.
`[voice]` stands in for the laryngeal features of stiffness and slackness. `[lateral]` is placed
at the supralaryngeal node, under which the Klamath evidence puts it; whether it hangs from that
node or from the place node is left open. `[sonorant]` and `[strident]`, which the dissertation
sets aside as acoustic, and the features it lacks are unplaced. The segments are specified as
the dissertation draws them, for the nodes and features under discussion and nothing else.

Spreading is `Finset.piecewise` on a node's feature class, so the target's own values under the
node are delinked. The geometry keeps the root, laryngeal, supralaryngeal and place nodes of
`Studies/Clements1985.lean` and has no manner node.

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

/-- The feature standing for an articulator node, `+` exactly when the articulator is active in
the segment. -/
def feature? : Node → Option Feature
  | .labial => some .labial
  | .coronal => some .coronal
  | .dorsal => some .dorsal
  | _ => none

/-- The articulator nodes under place. -/
def articulators : Finset Node := {.labial, .coronal, .dorsal}

theorem not_le_of_mem_articulators {a b : Node} (ha : a ∈ articulators) (hb : b ∈ articulators)
    (hab : a ≠ b) : ¬ a ≤ b := by
  revert a b; decide

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

/-! ### Spreading -/

/-- Spreading the class node `a` from `src` onto `tgt` gives `tgt` the values of `src`, specified
or not, for the features in the class of `a`, and leaves its other features. -/
def spread (a : Node) (src tgt : Segment) : Segment := .piecewise (featureClass node a) src tgt

variable (src tgt : Segment)

/-- Place assimilation gives the target the trigger's place features and leaves its degree of
closure, its nasality and its laryngeal features. -/
theorem spread_place :
    Set.EqOn (spread .place src tgt) src ↑(featureClass node .place) ∧
      Set.EqOn (spread .place src tgt) tgt
        ↑({.continuant, .consonantal, .nasal} ∪ featureClass node .laryngeal : Finset Feature) :=
  ⟨fun _ hf ↦ Finset.piecewise_eq_of_mem _ _ _ hf, Finset.eqOn_piecewise_of_disjoint (by decide)⟩

-- (30), (31a)
theorem spread_supralaryngeal :
    Set.EqOn (spread .supralaryngeal src tgt) src ↑({.nasal, .lateral} : Finset Feature) ∧
      Set.EqOn (spread .supralaryngeal src tgt) tgt ↑(featureClass node .laryngeal) :=
  ⟨Finset.eqOn_piecewise_of_subset (by decide), Finset.eqOn_piecewise_of_disjoint (by decide)⟩

/-- The prefix nasal of Kpelle, with no place of its own. -/
def nasalStop : Segment := [−continuant, +nasal]

/-- A labial fricative. -/
def labialFricative : Segment := [+continuant, +labial]

/-- A labial stop. -/
def labialStop : Segment := [−continuant, +labial]

/-- An alveolar fricative. -/
def alveolarFricative : Segment := [+continuant, +coronal, +anterior]

/-- (5): the labiovelar stop, a labial and a dorsal node under one place node. -/
def kp : Segment := [−continuant, +labial, +dorsal]

-- (19)
theorem spread_place_labialFricative_nasalStop :
    spread .place labialFricative nasalStop = [−continuant, +nasal, +labial] := by
  decide

-- (19)
theorem spread_place_kp_nasalStop :
    spread .place kp nasalStop = [−continuant, +nasal, +labial, +dorsal] := by
  decide

-- (22)
theorem spread_place_labialStop_alveolarFricative :
    spread .place labialStop alveolarFricative = [+continuant, +labial] := by
  decide

/-- (123): the Fanti trill. -/
def trill : Segment := [+coronal, −anterior, −distributed]

/-- (123): a high back rounded vowel. -/
def highBackRound : Segment := [+labial, +round, +dorsal, +back, +high]

-- (123)
theorem spread_dorsal_highBackRound_trill : spread .dorsal highBackRound trill =
    [+coronal, −anterior, −distributed, +dorsal, +back, +high] := by
  decide

/-! ### Complex segments -/

/-- A segment is licensed when every terminal feature it specifies under an articulator node,
whichever its value, has that articulator active. -/
def Licensed (s : Segment) : Prop :=
  ∀ f, (s f).isSome → ∀ n ∈ node f, ∀ g ∈ n.feature?, s g = some true

instance : DecidablePred Licensed := fun _ ↦ by unfold Licensed; infer_instance

variable {s : Segment}

theorem Licensed.ne_some_false (hs : Licensed s) {g : Feature}
    (hg : g ∈ Feature.majorArticulators) : s g ≠ some false := by
  have key : ∀ g ∈ Feature.majorArticulators, ∃ n ∈ node g, g ∈ n.feature? := by decide
  obtain ⟨n, hn, hgn⟩ := key g hg
  exact fun h ↦ absurd ((hs g (by simp [h]) n hn g hgn).symm.trans h) (by decide)

/-- A licensed segment specified for rounding that has a single articulator has the labial
one. -/
theorem articulators_eq_labial_of_round (hs : Licensed s) (hr : (s .round).isSome)
    (h : ¬ s.IsComplex) : s.articulators = {.labial} :=
  have hl : .labial ∈ s.articulators := by
    simp [Segment.articulators, hs .round hr .labial rfl .labial rfl]
  Finset.eq_singleton_iff_unique_mem.2
    ⟨hl, fun _ hx ↦ Finset.card_le_one.1 (not_lt.1 h) _ hx _ hl⟩

-- (2)
theorem isComplex_iff : s.IsComplex ↔ s.articulators ∈
    ({{.labial, .coronal}, {.labial, .dorsal}, {.coronal, .dorsal},
      {.labial, .coronal, .dorsal}} : Finset (Finset Feature)) := by
  have h : ∀ a b c : Bool,
      let t := Feature.majorArticulators.filter fun g ↦
        (g = .labial ∧ a) ∨ (g = .coronal ∧ b) ∨ (g = .dorsal ∧ c)
      1 < t.card ↔ t ∈ ({{.labial, .coronal}, {.labial, .dorsal}, {.coronal, .dorsal},
        {.labial, .coronal, .dorsal}} : Finset (Finset Feature)) := by
    decide
  have ht : s.articulators = Feature.majorArticulators.filter fun g ↦
      (g = .labial ∧ decide (s .labial = some true)) ∨
        (g = .coronal ∧ decide (s .coronal = some true)) ∨
          (g = .dorsal ∧ decide (s .dorsal = some true)) :=
    Finset.filter_congr fun g hg ↦ by
      rcases Feature.mem_majorArticulators.1 hg with rfl | rfl | rfl <;> simp
  unfold Segment.IsComplex
  rw [ht]
  exact h _ _ _

/-- (2): the labiocoronal stop. -/
def pt : Segment := [−continuant, +labial, +coronal]

/-- (2): a click, coronal and dorsal. -/
def click : Segment := [−continuant, +coronal, +dorsal]

/-- (65): the labiovelarized coronal stop of Kinyarwanda. -/
def tkw : Segment := [−continuant, +coronal, +labial, +round, +dorsal, +back]

/-- (14a): the rounded labial nasal of Aneityum. -/
def mw : Segment := [−continuant, +nasal, +labial, +round]

/-- (14d): the rounded `h` of Nenema, whose only articulator comes with its rounding. -/
def hw : Segment := [+spreadGlottis, +labial, +round]

-- (2), (5), (65)
theorem articulators_occlusions :
    kp.articulators = {.labial, .dorsal} ∧ pt.articulators = {.labial, .coronal} ∧
      click.articulators = {.coronal, .dorsal} ∧
        tkw.articulators = {.labial, .coronal, .dorsal} := by
  decide

-- (14a), (14d)
theorem licensed_mw_hw :
    Licensed mw ∧ ¬ mw.IsComplex ∧ Licensed hw ∧ ¬ hw.IsComplex ∧ Licensed tkw := by
  decide

theorem not_licensed : ¬ Licensed [+coronal, +round] ∧ ¬ Licensed [+labial, −coronal] := by
  decide

/-! ### Association lines -/

section Association

variable {ι : Type*} {τ : ι → Type*} {X : AR τ}

variable (X) in
/-- `X` can be placed in time with association as total simultaneity: intervals in the order of
each tier, equal across each line. -/
def HasSimultaneity : Prop :=
  ∃ (T : Type) (_ : LinearOrder T) (I : X.Pos → NonemptyInterval T),
    (∀ i ⦃p q : Fin (X.word i).length⦄, p < q → (I ⟨i, p⟩).Precedes (I ⟨i, q⟩)) ∧
      ∀ ⦃v w⦄, X.assoc.Adj v w → I v = I w

namespace HasSimultaneity

theorem hasIntervalOrder (h : HasSimultaneity X) : X.HasIntervalOrder := by
  obtain ⟨T, _, I, hI, hA⟩ := h
  exact AR.hasIntervalOrder_of_intervals I hI fun _ _ hvw ↦ by
    rw [hA hvw]
    exact NonemptyInterval.overlaps_refl _

private theorem lt_of_lt (h : HasSimultaneity X) {i j : ι} {p q p' q' : ℕ}
    (h₁ : X.Link i j p q) (h₂ : X.Link i j p' q') (hlt : p < p') : q < q' := by
  obtain ⟨T, _, I, hI, hA⟩ := h
  have hq := hI i (show (⟨p, h₁.lt_left⟩ : Fin _) < ⟨p', h₂.lt_left⟩ from hlt)
  rw [hA h₁.adj, hA h₂.adj] at hq
  by_contra! hge
  obtain rfl | hlt' := hge.eq_or_lt
  · exact NonemptyInterval.precedes_irrefl _ hq
  · exact NonemptyInterval.precedes_asymm hq
      (hI j (show (⟨q', h₂.lt_right⟩ : Fin _) < ⟨q, h₁.lt_right⟩ from hlt'))

/-- Read as simultaneity, the lines between two tiers pair their positions one to one and in
order. -/
theorem lt_iff_lt (h : HasSimultaneity X) {i j : ι} {p q p' q' : ℕ} (h₁ : X.Link i j p q)
    (h₂ : X.Link i j p' q') : p < p' ↔ q < q' :=
  ⟨h.lt_of_lt h₁ h₂, h.lt_of_lt h₁.symm h₂.symm⟩

end HasSimultaneity

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
theorem not_hasSimultaneity :
    ¬ HasSimultaneity contour ∧ ¬ HasSimultaneity geminate ∧ ¬ HasSimultaneity discontinuous :=
  ⟨fun h ↦ absurd ((h.lt_iff_lt (i := .upper) (j := .lower) (p := 0) (q := 0) (p' := 1) (q' := 0)
      (by decide) (by decide)).1 (by decide)) (by decide),
    fun h ↦ absurd ((h.lt_iff_lt (i := .upper) (j := .lower) (p := 0) (q := 0) (p' := 0) (q' := 1)
      (by decide) (by decide)).2 (by decide)) (by decide),
    fun h ↦ absurd ((h.lt_iff_lt (i := .upper) (j := .lower) (p := 0) (q := 0) (p' := 0) (q' := 2)
      (by decide) (by decide)).2 (by decide)) (by decide)⟩

-- (18), (21)
theorem hasIntervalOrder_contour_geminate_discontinuous :
    contour.HasIntervalOrder ∧ geminate.HasIntervalOrder ∧ discontinuous.HasIntervalOrder :=
  ⟨(AR.noCrossing_iff_hasIntervalOrder_of_card_le_two (by simp)).1 (by decide),
    (AR.noCrossing_iff_hasIntervalOrder_of_card_le_two (by simp)).1 (by decide),
    (AR.noCrossing_iff_hasIntervalOrder_of_card_le_two (by simp)).1 (by decide)⟩

/-- (23): the representation with crossed lines cannot be placed in time with association as
overlap. -/
theorem not_hasIntervalOrder_crossing : ¬ crossing.HasIntervalOrder :=
  fun h ↦ absurd h.noCrossing (by decide)

end Sagey1986
