module

public import Linglib.Core.Order.LeftLinear
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Defs

/-!
# Feature geometry

A feature geometry over a feature type `F` hangs each feature from at most one node of a tree of
class nodes, a map `node : F → Option N`, where `a ≤ b` when node `a` dominates node `b`. The
[feature class](##Phonology.FeatureGeometry.featureClass) of a node is the set of features hanging
at or below it, [the preimage](##Phonology.FeatureGeometry.coe_featureClass) of the subtree
`Set.Ici a` under the node. Feature classes therefore
[shrink along dominance](##Phonology.FeatureGeometry.antitone_featureClass) and, in a tree, are
[disjoint across incomparable nodes](##Phonology.FeatureGeometry.disjoint_featureClass).
Assimilation spreads a class from one segment onto another, `Finset.piecewise` on the class, so
spreading a node
[carries every class it dominates](##Phonology.FeatureGeometry.eqOn_piecewise_of_le) and [leaves every incomparable class
untouched](##Phonology.FeatureGeometry.eqOn_piecewise_of_incompRel).

## Implementation notes

The placement is `Option`-valued so that a geometry may leave features of the inventory
unplaced. A tree is a left-linear order, which mathlib's rooted trees are. A set of features is
exhaustively dominated by a node, in Halle, Vaux and Wolfe's sense, when it is the node's feature
class; single-feature spreading is `Function.update`.

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

variable {F N : Type*} [Fintype F]

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

/-! ### Spreading -/

variable [DecidableEq F] {β : Type*} (src tgt : F → β)

/-- Spreading node `a` from `src` onto `tgt` carries every class `a` dominates. -/
theorem eqOn_piecewise_of_le (h : a ≤ b) :
    Set.EqOn ((featureClass node a).piecewise src tgt) src ↑(featureClass node b) :=
  fun _ hg ↦ Finset.piecewise_eq_of_mem _ _ _ (antitone_featureClass h hg)

end Preorder

section LeftLinear

variable [PartialOrder N] [IsLeftLinear N] [DecidableLE N] {node : F → Option N} {a b : N}

/-- Incomparable nodes of a tree have disjoint feature classes, since their subtrees are
disjoint. -/
theorem disjoint_featureClass (h : IncompRel (· ≤ ·) a b) :
    Disjoint (featureClass node a) (featureClass node b) :=
  Finset.disjoint_coe.1 <| by
    simpa only [coe_featureClass] using ((Set.disjoint_image_iff (Option.some_injective N)).2
      (IsLeftLinear.disjoint_Ici_iff.2 h)).preimage node

variable [DecidableEq F] {β : Type*} (src tgt : F → β)

/-- Spreading node `a` leaves every class incomparable with `a` untouched. -/
theorem eqOn_piecewise_of_incompRel (h : IncompRel (· ≤ ·) a b) :
    Set.EqOn ((featureClass node a).piecewise src tgt) tgt ↑(featureClass node b) :=
  fun _ hg ↦
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_featureClass h) hg)

end LeftLinear

end Phonology.FeatureGeometry
