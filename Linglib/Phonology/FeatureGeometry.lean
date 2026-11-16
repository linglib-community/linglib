module

public import Linglib.Core.Order.Laminar
public import Linglib.Core.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Defs

/-!
# Feature geometry

A feature geometry over a feature type `F` hangs each feature from at most one node of a tree of
class nodes, a map `node : F → Option N`, where `a ≤ b` when node `a` dominates node `b`. The
[feature class](##Phonology.FeatureGeometry.featureClass) of a node is the set of features hanging
at or below it, [the preimage](##Phonology.FeatureGeometry.coe_featureClass) of the subtree
`Set.Ici a` under the node. Feature classes therefore
[shrink along dominance](##Phonology.FeatureGeometry.antitone_featureClass) and, in a tree, are
[disjoint across incomparable nodes](##Phonology.FeatureGeometry.disjoint_featureClass), so that
[no two overlap](##Phonology.FeatureGeometry.isLaminar_range_featureClass) unless one contains
the other, the condition Padgett carries over to classes taken as bare sets of features.
Assimilation spreads a class from one segment onto another, `Finset.piecewise` on the class, and
when classes do not overlap it [carries or leaves whole](##IsLaminar.subset_or_eqOn_piecewise)
every class that does not properly contain the one spread.

## Implementation notes

The placement is `Option`-valued so that a geometry may leave features of the inventory
unplaced. A tree is a left-linear order, which mathlib's rooted trees are. A set of features is
exhaustively dominated by a node, in Halle, Vaux and Wolfe's sense, when it is the node's feature
class; single-feature spreading is `Function.update`.

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

variable (node) in
/-- The feature classes of a tree do not overlap: any two are nested or disjoint. -/
theorem isLaminar_range_featureClass : IsLaminar (Set.range (featureClass node)) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  by_cases hab : a ≤ b
  · exact .inr (.inl (antitone_featureClass hab))
  by_cases hba : b ≤ a
  · exact .inl (antitone_featureClass hba)
  · exact .inr (.inr (disjoint_featureClass ⟨hab, hba⟩))

end LeftLinear

end Phonology.FeatureGeometry

/-! ### Spreading -/

/-- Spreading a class `s` of a family whose classes do not overlap carries a class `t` whole or
leaves it whole, unless `t` contains `s`. -/
theorem IsLaminar.subset_or_eqOn_piecewise {F β : Type*} [DecidableEq F] {S : Set (Finset F)}
    (hS : IsLaminar S) {s t : Finset F} (hs : s ∈ S) (ht : t ∈ S) (src tgt : F → β) :
    s ⊆ t ∨ Set.EqOn (s.piecewise src tgt) src ↑t ∨ Set.EqOn (s.piecewise src tgt) tgt ↑t :=
  (hS hs ht).imp_right <| .imp Finset.eqOn_piecewise_of_subset Finset.eqOn_piecewise_of_disjoint
