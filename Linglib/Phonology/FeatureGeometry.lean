module

public import Mathlib.Order.Comparable
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Data.Finset.Piecewise

/-!
# Feature geometry

A feature geometry over a feature type `F` places each feature below at most one node of a
rooted tree of class nodes, a map `node : F → Option N`, and the feature class of a node is
the set of features placed at or below it. The tree is mathlib's, a partial order with a
bottom, a predecessor and archimedean descent, so feature classes are the preimages of
principal upper sets: they shrink along dominance and are disjoint across incomparable nodes.
Spreading a class from one segment onto another is `Finset.piecewise` on it, and agreement on
a class is `Set.EqOn`. The trees of Clements, Sagey and Halle, Vaux and Wolfe are built in
their studies.

## Main definitions

* `FeatureGeometry.featureClass` — the features a placement puts at or below a node.

## Main results

* `antitone_featureClass`, `disjoint_featureClass` — feature classes shrink along dominance
  and are disjoint across incomparable nodes.
* `eqOn_piecewise_of_le`, `eqOn_piecewise_of_incompRel` — spreading a node carries every
  class it dominates and leaves every incomparable class untouched.

## Implementation notes

The placement is `Option`-valued so that a geometry may leave features of the inventory
unplaced. A study orders its tree by the parent map, `a ≤ b` when `a` lies on the walk from `b`
up to the root, the root as `⊥` and the parent as `Order.pred`, every axiom decided. Spreading
any set of terminals, Halle, Vaux and Wolfe's partial spreading, is `Finset.piecewise` on that
set, and single-feature spreading is `Function.update`.

## References

* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
* [J. Padgett, *Feature Classes in Phonology* (2002)][padgett-2002]
* [J. Brown and J. Meyer, *Assimilation and Morpheme Boundaries in Mgira* (2024)][brown-meyer-2024]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

@[expose] public section

namespace Phonology.FeatureGeometry

variable {F N : Type*} [Fintype F] [Preorder N] [DecidableLE N] (node : F → Option N)

/-! ### Feature classes -/

/-- The feature class of a node is the set of features placed at or below it. -/
def featureClass (a : N) : Finset F :=
  Finset.univ.filter fun f ↦ ∃ m ∈ node f, a ≤ m

variable {node} {a b : N} {f : F}

theorem mem_featureClass : f ∈ featureClass node a ↔ ∃ m ∈ node f, a ≤ m := by
  simp [featureClass]

/-- The root's class is every placed feature, so spreading the root is total assimilation. -/
theorem mem_featureClass_bot [OrderBot N] : f ∈ featureClass node ⊥ ↔ (node f).isSome := by
  simp [mem_featureClass, Option.isSome_iff_exists]

/-- Feature classes shrink along dominance. -/
theorem antitone_featureClass : Antitone (featureClass node) := fun _ _ h _ hg ↦ by
  rw [mem_featureClass] at hg ⊢
  obtain ⟨m, hm, hbm⟩ := hg
  exact ⟨m, hm, h.trans hbm⟩

/-- Incomparable nodes have disjoint feature classes, since their subtrees are disjoint. -/
theorem disjoint_featureClass [PredOrder N] [IsPredArchimedean N] (h : IncompRel (· ≤ ·) a b) :
    Disjoint (featureClass node a) (featureClass node b) := by
  rw [Finset.disjoint_left]
  intro g hga hgb
  rw [mem_featureClass] at hga hgb
  obtain ⟨m, hm, ham⟩ := hga
  obtain ⟨m', hm', hbm⟩ := hgb
  rw [Option.mem_def] at hm hm'
  rw [hm, Option.some.injEq] at hm'
  subst hm'
  exact (le_total_of_directed ham hbm).elim h.2 h.1

/-! ### Spreading -/

variable [DecidableEq F] {β : Type*} (src tgt : F → β)

/-- Spreading node `a` from `src` onto `tgt` carries every class `a` dominates. -/
theorem eqOn_piecewise_of_le (h : a ≤ b) :
    Set.EqOn ((featureClass node a).piecewise src tgt) src ↑(featureClass node b) :=
  fun _ hg ↦ Finset.piecewise_eq_of_mem _ _ _ (antitone_featureClass h hg)

/-- Spreading node `a` leaves every class incomparable with `a` untouched. -/
theorem eqOn_piecewise_of_incompRel [PredOrder N] [IsPredArchimedean N]
    (h : IncompRel (· ≤ ·) a b) :
    Set.EqOn ((featureClass node a).piecewise src tgt) tgt ↑(featureClass node b) :=
  fun _ hg ↦
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_featureClass h) hg)

end Phonology.FeatureGeometry
