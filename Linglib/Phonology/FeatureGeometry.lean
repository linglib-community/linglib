module

public import Linglib.Core.Order.Laminar
public import Linglib.Core.Data.Finset.Piecewise
public import Linglib.Phonology.Segmental.Defs
public import Mathlib.Data.Fintype.Defs

/-!
# Feature geometry

A feature geometry over a feature type `F` hangs each feature from at most one node of a tree of
class nodes, a map `node : F → Option N`, where `a ≤ b` when node `a` dominates node `b`. The
feature class of a node, `featureClass node a`, is the set of features hanging at or below it,
the preimage of the subtree `Set.Ici a` under `node` (`coe_featureClass`). Feature classes shrink
along dominance (`antitone_featureClass`) and, in a tree, are disjoint across incomparable nodes
(`disjoint_featureClass`), so that no two overlap unless one contains the other
(`isLaminar_range_featureClass`), the condition Padgett carries over to classes taken as bare
sets of features.

A partial specification of the features, such as a segment, bears a node when it specifies a
feature at or below it, `Bears node s a`. The nodes a specification bears are closed under
domination (`isLowerSet_setOf_bears`): with a node come the nodes above it, as the feature content
of a pronoun is a lower set of the tree of `Morphology/FeatureGeometry.lean`.

Assimilation spreads a node from one specification onto another: `spread node a src tgt` has the
values of `src` on the class of `a` and those of `tgt` elsewhere. It carries whole every node
that `a` dominates (`spread_eqOn_of_le`) and, in a tree, leaves whole every node incomparable to
`a` (`spread_eqOn_of_incompRel`), so the result bears the former as the source does and the
latter as the target does (`bears_spread_of_le`, `bears_spread_of_incompRel`).

## Implementation notes

The placement is `Option`-valued so that a geometry may leave features of the inventory
unplaced. A tree is a forest order, which mathlib's rooted trees are. A set of features is
exhaustively dominated by a node, in Halle, Vaux and Wolfe's sense, when it is the node's feature
class; single-feature spreading is `Function.update`.

A class node has no value of its own. Whether a specification has a node is read from the
features it specifies, so a geometry that needs a node with no terminal feature under it places a
feature at the node to stand for it. `Phonology.Segment.spread` is `spread` on segments.

## TODO

Spreading here acts on each feature of a class separately. Whether a rule moves a class node as a
unit, so that blocking one feature blocks the class, or targets the features one by one, the
point on which Clements differs from Padgett and from Halle, Vaux and Wolfe, is not represented.

## References

* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
* [J. Padgett, *Feature Classes in Phonology* (2002)][padgett-2002]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

@[expose] public section

namespace Phonology.FeatureGeometry

variable {F N β : Type*} [Fintype F]

section Preorder

variable [Preorder N] [DecidableLE N] (node : F → Option N)

/-! ### Feature classes -/

/-- The feature class of a node is the set of features placed at or below it. -/
def featureClass (a : N) : Finset F :=
  Finset.univ.filter fun f ↦ ∃ m ∈ node f, a ≤ m

variable {node} {a b : N} {f : F}

theorem mem_featureClass : f ∈ featureClass node a ↔ ∃ m ∈ node f, a ≤ m := by
  simp [featureClass]

/-- The feature class of a node is the preimage of the subtree under it. -/
theorem coe_featureClass : (featureClass node a : Set F) = node ⁻¹' (some '' Set.Ici a) := by
  ext f
  simp [mem_featureClass, and_comm, eq_comm]

theorem le_of_mem_featureClass {m : N} (h : f ∈ featureClass node a) (hf : node f = some m) :
    a ≤ m := by
  simpa [mem_featureClass, hf] using h

/-- Feature classes shrink along dominance. -/
theorem antitone_featureClass : Antitone (featureClass node) := fun _ _ h ↦
  Finset.coe_subset.1 <| by
    simpa only [coe_featureClass] using
      Set.preimage_mono (Set.image_mono (Set.Ici_subset_Ici.2 h))

/-! ### The nodes of a specification -/

variable (node) in
/-- A partial specification of the features bears a node when it specifies a feature placed at
or below it. -/
def Bears (s : F → Option β) (a : N) : Prop := ∃ f ∈ featureClass node a, (s f).isSome

instance (s : F → Option β) (a : N) : Decidable (Bears node s a) :=
  inferInstanceAs (Decidable (∃ f ∈ featureClass node a, (s f).isSome))

section Bears

variable {s : F → Option β}

theorem Bears.of_le (h : Bears node s b) (hab : a ≤ b) : Bears node s a :=
  let ⟨f, hf, hs⟩ := h
  ⟨f, antitone_featureClass hab hf, hs⟩

/-- The nodes a specification bears are closed under domination. -/
theorem isLowerSet_setOf_bears : IsLowerSet {a | Bears node s a} := fun _ _ hab h ↦ h.of_le hab

/-- A specified feature brings its node and every node above it. -/
theorem bears_of_isSome {m : N} (hf : node f = some m) (hs : (s f).isSome) (ham : a ≤ m) :
    Bears node s a :=
  ⟨f, mem_featureClass.2 ⟨m, hf, ham⟩, hs⟩

end Bears

/-! ### Spreading -/

section Spread

variable [DecidableEq F]

variable (node) in
/-- Spreading the node `a` from `src` onto `tgt` gives `tgt` the values of `src`, specified or
not, on the feature class of `a`. -/
def spread (a : N) (src tgt : F → β) : F → β := (featureClass node a).piecewise src tgt

variable {src tgt : F → β}

theorem spread_eqOn : Set.EqOn (spread node a src tgt) src ↑(featureClass node a) :=
  Finset.eqOn_piecewise_of_subset subset_rfl

theorem spread_of_mem (hf : f ∈ featureClass node a) : spread node a src tgt f = src f :=
  Finset.piecewise_eq_of_mem _ _ _ hf

theorem spread_of_notMem (hf : f ∉ featureClass node a) : spread node a src tgt f = tgt f :=
  Finset.piecewise_eq_of_notMem _ _ _ hf

/-- Spreading a node carries whole every node it dominates. -/
theorem spread_eqOn_of_le (h : a ≤ b) :
    Set.EqOn (spread node a src tgt) src ↑(featureClass node b) :=
  Finset.eqOn_piecewise_of_subset (antitone_featureClass h)

theorem bears_spread_of_le {src tgt : F → Option β} (h : a ≤ b) :
    Bears node (spread node a src tgt) b ↔ Bears node src b :=
  exists_congr fun _ ↦ and_congr_right fun hf ↦ by
    rw [spread_eqOn_of_le h (Finset.mem_coe.2 hf)]

end Spread

end Preorder

section ForestOrder

variable [PartialOrder N] [IsForestOrder N] [DecidableLE N] {node : F → Option N} {a b : N}

/-- Incomparable nodes of a tree have disjoint feature classes, since their subtrees are
disjoint. -/
theorem disjoint_featureClass (h : IncompRel (· ≤ ·) a b) :
    Disjoint (featureClass node a) (featureClass node b) :=
  Finset.disjoint_coe.1 <| by
    simpa only [coe_featureClass] using ((Set.disjoint_image_iff (Option.some_injective N)).2
      (IsForestOrder.disjoint_Ici_iff.2 h)).preimage node

variable (node) in
/-- The feature classes of a tree do not overlap: any two are nested or disjoint. -/
theorem isLaminar_range_featureClass : IsLaminar (Set.range (featureClass node)) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  by_cases hab : a ≤ b
  · exact .inr (.inl (antitone_featureClass hab))
  by_cases hba : b ≤ a
  · exact .inl (antitone_featureClass hba)
  · exact .inr (.inr (disjoint_featureClass ⟨hab, hba⟩))

section Spread

variable [DecidableEq F]

/-- In a tree, spreading a node leaves whole every node incomparable to it. -/
theorem spread_eqOn_of_incompRel {src tgt : F → β} (h : IncompRel (· ≤ ·) a b) :
    Set.EqOn (spread node a src tgt) tgt ↑(featureClass node b) :=
  Finset.eqOn_piecewise_of_disjoint (disjoint_featureClass h)

theorem bears_spread_of_incompRel {src tgt : F → Option β} (h : IncompRel (· ≤ ·) a b) :
    Bears node (spread node a src tgt) b ↔ Bears node tgt b :=
  exists_congr fun _ ↦ and_congr_right fun hf ↦ by
    rw [spread_eqOn_of_incompRel h (Finset.mem_coe.2 hf)]

end Spread

end ForestOrder

end Phonology.FeatureGeometry

namespace Phonology.Segment

variable {N : Type*} [Preorder N] [DecidableLE N] (node : Feature → Option N) (a : N)
  (src tgt : Segment)

/-- Spreading the node `a` from the segment `src` onto the segment `tgt`. -/
def spread : Segment := ⟨FeatureGeometry.spread node a src.val tgt.val⟩

@[simp] theorem coe_spread :
    ⇑(spread node a src tgt) = FeatureGeometry.spread node a ⇑src ⇑tgt := rfl

end Phonology.Segment

/-! ### Spreading -/

/-- Spreading a class `s` of a family whose classes do not overlap carries a class `t` whole or
leaves it whole, unless `t` contains `s`. -/
theorem IsLaminar.subset_or_eqOn_piecewise {F β : Type*} [DecidableEq F] {S : Set (Finset F)}
    (hS : IsLaminar S) {s t : Finset F} (hs : s ∈ S) (ht : t ∈ S) (src tgt : F → β) :
    s ⊆ t ∨ Set.EqOn (s.piecewise src tgt) src ↑t ∨ Set.EqOn (s.piecewise src tgt) tgt ↑t :=
  (hS hs ht).imp_right <| .imp Finset.eqOn_piecewise_of_subset Finset.eqOn_piecewise_of_disjoint
