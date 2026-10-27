module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Morphology.Word.Basic
public import Linglib.Data.Treebank.Coverage.KuhlmannNivre2006
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Kuhlmann & Nivre (2006): Mildly Non-Projective Dependency Structures

This file formalizes the paper's comparison of the constraints proposed for mildly
non-projective dependency structures: planarity, well-nestedness, gap degree, and the edge
degree of [nivre-2006]. The first three, with the dominance and projection they are stated
through, are the substrate of `Syntax/DependencyGrammar/`, whose definitions follow the paper;
edge degree, the number of constituents an edge spans without dominating, is `edgeDegree`, and
`edgeDegree_eq_zero_iff` proves for it the paper's observation that degree zero is
projectivity, as `Graph.isProjective_iff_gapDegree_eq_zero` proves it for gap degree. The
hierarchy projective ⊂ planar ⊂ well-nested is the substrate's, proved there for the paper's
dependency forests, of which Figure 1 is one with two roots (`fig1_isForest_not_isTree`); the
paper's figures supply the witnesses that keep the inclusions strict, that separate the two
graded measures, and that show well-nestedness independent of both.

The counts of Table 1 are the rows of `Data/Treebank/Coverage/KuhlmannNivre2006.json`, over
which the paper's percentages are recomputed: about 15% of the Danish and 23% of the Prague
trees are non-projective (`nonProjective_share`), a degree bound of one covers more than 98% of
both treebanks on either measure (`degreeLe1_coverage`), and among the non-projective trees
planarity covers fewer than a quarter while well-nestedness covers more than 99%
(`nonProjective_binary`).

## Implementation notes

Positions are zero-based, so node `i` of a figure is position `i - 1`. A connected component
of the subgraph an edge's span induces is identified by its root, the position of the span with
no head inside it, so the degree of an edge counts those positions its head does not dominate.
The trees of the figures are read off the drawings, and the paper's remarks about them, the
projections of the nodes marked `i`, the edges of degree one, and the interleaving subtrees, are
proved of the reconstructions.
Percentages are recomputed from the rows as rounded hundredths of a percent, the precision the
paper prints, and the subtable over non-projective trees is the difference from the projective
row, since planarity and well-nestedness each contain projectivity.

## TODO

* The paper gives the coverage of edge degree at most one on DDT as 98.24%, the sum of the
  printed 84.95% and 13.29%; the rows give 98.25%.

## References

* [kuhlmann-nivre-2006]
* [nivre-2006]
-/

@[expose] public section

namespace KuhlmannNivre2006

open DependencyGrammar Relation
open Morphology (Word)

variable {n : ℕ} (g : Graph n)

/-! ### Edge degree (Definition 9) -/

/-- The roots of the connected components of the subgraph induced by the span of the arc from
`h` to `d`: the positions of the span with no head inside it. -/
def componentRoots (h d : Fin n) : Finset (Fin n) :=
  (Finset.uIcc h d).filter fun v ↦ ∀ u, g.Adj u v → u ∉ Finset.uIcc h d

/-- The degree of the arc from `h` to `d`: the number of components of the subgraph induced by
its span whose root `h` does not dominate. -/
def edgeDegreeAt (h d : Fin n) : ℕ :=
  ((componentRoots g h d).filter fun v ↦ ¬ Dominates g h v).card

/-- The edge degree of a graph: the maximum degree of its arcs. -/
def edgeDegree : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n ↦ g.Adj p.1 p.2).sup fun p ↦ edgeDegreeAt g p.1 p.2

variable {g}

theorem edgeDegreeAt_eq_zero_iff (hT : g.IsTree) {h d : Fin n} :
    edgeDegreeAt g h d = 0 ↔ ∀ v ∈ Set.uIcc h d, Dominates g h v := by
  rw [edgeDegreeAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [componentRoots, Finset.mem_filter, not_not, and_imp]
  simp only [← Finset.mem_coe, Finset.coe_uIcc]
  constructor
  · intro H v hv
    by_cases hr : g.root ∈ Set.uIcc h d
    · exact (hT.dominates_antisymm (H hr fun u hu ↦ absurd hu (hT.not_adj_root u))
        (hT.root_dominates h)).symm ▸ hT.root_dominates v
    · obtain ⟨p, q, hpq, hp, hq, -, hqv⟩ :=
        (hT.root_dominates v).exists_boundary (S := (Set.uIcc h d)ᶜ) hr (not_not_intro hv)
      exact (H (not_not.mp hq) fun u hu ↦ hT.leftUnique_adj hu hpq ▸ hp).trans hqv
  · exact fun H v hv _ ↦ H v hv

theorem edgeDegree_eq_zero_iff (hT : g.IsTree) : edgeDegree g = 0 ↔ g.IsProjective := by
  rw [Graph.isProjective_iff_isArcProjective, edgeDegree, ← Nat.bot_eq_zero,
    Finset.sup_eq_bot_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.bot_eq_zero, Prod.forall,
    edgeDegreeAt_eq_zero_iff hT]
  exact Iff.rfl

/-! ### Figure 1: a dependency forest

The analysis of *Není proto zapotřebí uzavírat nové nájemní smlouvy.* leaves *proto* and the final
punctuation mark without a head, so it is a forest and not a tree, and the yield of *není* skips
*proto*. -/

/-- An unlabelled position. -/
def dot : Word := Word.mk' "•" .X

/-- Figure 1: nodes 2 and 8 have no head. -/
def fig1 : Graph 8 :=
  .ofArcs [dot, dot, dot, dot, dot, dot, dot, dot] 1
    [(1, 0, .dep), (0, 2, .dep), (0, 3, .dep), (3, 6, .dep), (6, 4, .dep), (6, 5, .dep)]

/-- Figure 1 is a forest whose roots are nodes 2 and 8, and so not a tree. -/
theorem fig1_isForest_not_isTree :
    fig1.IsForest ∧ ¬ fig1.IsTree ∧ ∀ w, (∀ v, ¬ fig1.Adj v w) ↔ w = 1 ∨ w = 7 := by
  decide

-- Figure 1
theorem fig1_not_isProjective :
    fig1.projection 0 = [0, 2, 3, 4, 5, 6] ∧ ¬ fig1.IsProjective := by
  decide

/-! ### Figure 2: planarity

Figure 2a is planar but not projective, its root inside the gap where the substrate's
`Graph.IsPlanar.root_mem_gap` says a planar tree's root has to be; Figure 2b is not planar,
its two named edges crossing. -/

/-- Figure 2a: the yield of node 1, `{1, 3}`, skips the root. -/
def fig2a : Graph 3 := .ofArcs [dot, dot, dot] 1 [(1, 0, .dep), (0, 2, .dep)]

/-- Figure 2b: the edges (1, 4) and (3, 5) cross. -/
def fig2b : Graph 5 :=
  .ofArcs [dot, dot, dot, dot, dot] 1 [(1, 0, .dep), (0, 3, .dep), (3, 2, .dep), (2, 4, .dep)]

theorem fig2a_isTree : fig2a.IsTree := by decide
theorem fig2b_isTree : fig2b.IsTree := by decide

theorem fig2a_planar_not_projective :
    fig2a.IsPlanar ∧ ¬ fig2a.IsProjective ∧ (0 : Fin 3) < fig2a.root ∧ fig2a.root < 2 := by
  decide

-- Figure 2b, (1, 4), (3, 5)
theorem fig2b_crossing :
    fig2b.Linked 0 3 ∧ fig2b.Linked 2 4 ∧ Alternate (0 : Fin 5) 3 2 4 ∧ fig2b.crossings = 1 := by
  decide +kernel

/-! ### Figure 3: gap degree, edge degree, and well-nestedness -/

/-- Figure 3a: the projection of node 2 is the interval `(2, 3, 4)`. -/
def fig3a : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, .dep), (1, 2, .dep), (2, 3, .dep), (0, 4, .dep), (4, 5, .dep)]

/-- Figure 3b: the projection of node 2 is `(2, 3, 6)`, with the gap `(3, 6)`. -/
def fig3b : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, .dep), (1, 2, .dep), (2, 5, .dep), (0, 3, .dep), (3, 4, .dep)]

/-- Figure 3c: the projection of node 2 is `(2, 4, 6)`, with the gaps `(2, 4)` and `(4, 6)`. -/
def fig3c : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, .dep), (1, 3, .dep), (3, 5, .dep), (0, 2, .dep), (2, 4, .dep)]

theorem figure3_isTree : fig3a.IsTree ∧ fig3b.IsTree ∧ fig3c.IsTree := by decide

theorem figure3_gapDegree :
    (fig3a.gapDegreeAt 1 = 0 ∧ fig3a.gapDegree = 0) ∧
      (fig3b.gapDegreeAt 1 = 1 ∧ fig3b.gapDegree = 1) ∧
        (fig3c.gapDegreeAt 1 = 2 ∧ fig3c.gapDegree = 2) := by
  decide +kernel

-- (1, 5), Figure 3a, (3, 6), Figure 3b, (2, 4), (3, 5), (4, 6), Figure 3c
theorem figure3_edgeDegree :
    (edgeDegreeAt fig3a 0 4 = 0 ∧ edgeDegree fig3a = 0) ∧
      (edgeDegreeAt fig3b 2 5 = 1 ∧ edgeDegree fig3b = 1) ∧
        (edgeDegreeAt fig3c 1 3 = 1 ∧ edgeDegreeAt fig3c 2 4 = 1 ∧ edgeDegreeAt fig3c 3 5 = 1 ∧
          edgeDegree fig3c = 1) := by
  decide +kernel

-- Figures 3a and 3b, Figure 3c
theorem figure3_wellNested :
    fig3a.IsWellNested ∧ fig3b.IsWellNested ∧
      (fig3c.Interleave 1 2 ∧ ¬ Dominates fig3c 1 2 ∧ ¬ Dominates fig3c 2 1) := by
  decide +kernel

-- Figure 2a, Figure 3b
theorem hierarchy_strict :
    (fig2a.IsPlanar ∧ ¬ fig2a.IsProjective) ∧ (fig3b.IsWellNested ∧ ¬ fig3b.IsPlanar) := by
  decide +kernel

/-! ### Figure 4: gap degree against edge degree -/

/-- Figure 4a: the subtree at node 2 has two gaps, each of its edges spanning one component
node 2 does not dominate. -/
def fig4a : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, .dep), (0, 2, .dep), (2, 4, .dep), (1, 3, .dep), (3, 5, .dep)]

/-- Figure 4b: the subtree at node 2 has one gap, containing two components node 2 does not
dominate. -/
def fig4b : Graph 5 :=
  .ofArcs [dot, dot, dot, dot, dot] 0 [(0, 1, .dep), (0, 2, .dep), (0, 3, .dep), (1, 4, .dep)]

theorem figure4_isTree : fig4a.IsTree ∧ fig4b.IsTree := by decide

-- Figure 4
theorem figure4_degrees :
    (fig4a.gapDegreeAt 1 = 2 ∧ fig4a.gapDegree = 2 ∧ edgeDegree fig4a = 1) ∧
      (fig4b.gapDegreeAt 1 = 1 ∧ fig4b.gapDegree = 1 ∧ edgeDegreeAt fig4b 1 4 = 2 ∧
        edgeDegree fig4b = 2) := by
  decide +kernel

/-! ### Table 1: coverage on the Danish and Prague treebanks -/

open Data.Treebank.Coverage

/-- The rows of Table 1. -/
abbrev rows : List Row := Data.Treebank.Coverage.KuhlmannNivre2006.rows

/-- The number of trees of a treebank meeting a constraint. -/
def count (treebank : String) (c : Constraint) : ℕ :=
  match rows.find? fun r ↦ r.treebank = treebank ∧ r.constraint = c with
  | some r => r.value
  | none => 0

/-- The number of trees of a treebank. -/
def total (treebank : String) : ℕ :=
  match rows.find? (·.treebank = treebank) with
  | some r => r.total
  | none => 0

/-- The number of trees of degree at most `k` on a graded measure. -/
def atMost (treebank : String) (measure : ℕ → Constraint) (k : ℕ) : ℕ :=
  ((List.range (k + 1)).map fun d ↦ count treebank (measure d)).sum

/-- The number of non-projective trees of a treebank. -/
def nonProjective (treebank : String) : ℕ := total treebank - count treebank .projective

/-- A share in hundredths of a percent, rounded as the paper prints it. -/
def shareBp (num den : ℕ) : ℤ := round ((num : ℚ) / den * 10000)

theorem nonProjective_share :
    shareBp (nonProjective "DDT") (total "DDT") = 1505 ∧
      shareBp (nonProjective "PDT") (total "PDT") = 2315 := by
  decide +kernel

theorem degreeLe1_coverage :
    (shareBp (atMost "DDT" .gapDegreeEq 1) (total "DDT") = 9984 ∧
      shareBp (atMost "PDT" .gapDegreeEq 1) (total "PDT") = 9957) ∧
    (shareBp (atMost "DDT" .edgeDegreeEq 1) (total "DDT") = 9825 ∧
      shareBp (atMost "PDT" .edgeDegreeEq 1) (total "PDT") = 9954) := by
  decide +kernel

theorem nonProjective_binary :
    (shareBp (count "DDT" .planar - count "DDT" .projective) (nonProjective "DDT") = 968 ∧
      shareBp (count "PDT" .planar - count "PDT" .projective) (nonProjective "PDT") = 2293) ∧
    (shareBp (count "DDT" .wellNested - count "DDT" .projective) (nonProjective "DDT") = 9924 ∧
      shareBp (count "PDT" .wellNested - count "PDT" .projective) (nonProjective "PDT") =
        9954) := by
  decide +kernel

end KuhlmannNivre2006
