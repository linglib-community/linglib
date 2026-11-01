module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Morphology.Word.Basic
public import Linglib.Data.Statistics.KuhlmannNivre2006
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Kuhlmann & Nivre (2006): Mildly Non-Projective Dependency Structures

This file formalizes the paper's comparison of the constraints proposed for mildly
non-projective dependency structures: planarity, well-nestedness, gap degree, and the edge
degree of [nivre-2006]. The first three, with the dominance and projection they are stated
through, are the substrate of `Syntax/DependencyGrammar/`, whose definitions follow the paper;
edge degree, the number of constituents an edge spans without dominating, is `edgeDegree`, and
[degree zero is projectivity](##edgeDegree_eq_zero_iff) on it as on gap degree. The hierarchy
projective ⊂ planar ⊂ well-nested is the substrate's, proved there for the paper's dependency
forests, of which [Figure 1 is one with two roots](##fig1_isForest_not_isTree); the paper's
figures supply the witnesses that keep the inclusions strict, that separate the two graded
measures, and that show well-nestedness independent of both.

Table 1 counts the structures of the Danish and the Prague Dependency Treebank at each degree
and under each binary constraint. On a treebank of trees with the table's counts over all
structures, [copies of the paper's own figures making one](##exists_hasCounts), the degree-zero
theorems fix [the rows at degree zero](##HasCounts.countP_degree_eq_zero) and the hierarchy
fixes [the rows over the non-projective structures](##HasCounts.countP_nonProjective). The
text's percentages are recomputed from the counts: about 15% of the Danish and 23% of the Prague
trees are non-projective, [gap degree 2 and edge degree 4 cover all of the Danish trees, gap
degree 4 and edge degree 6 all of the Prague ones](##isLeast_atMost_eq_all), a degree bound of
one covers more than 98% of both on either measure, and among the non-projective trees planarity
covers fewer than a quarter while well-nestedness covers more than 99%.

## Implementation notes

Positions are zero-based, so node `i` of a figure is position `i - 1`. A connected component
of the subgraph an edge's span induces is identified by its root, the position of the span with
no head inside it, so the degree of an edge counts those positions its head does not dominate.
The trees of the figures are read off the drawings, and the paper's remarks about them, the
projections of the nodes marked `i`, the edges of degree one, and the interleaving subtrees, are
proved of the reconstructions. A treebank is a multiset of graphs, each on the positions of its
own sentence, and a dash in Table 1 is a count of zero. A percentage of the text is compared with
the counts by `Decimal.RoundsPercent`, at the precision the text prints it.

## Errata

* The text gives the coverage of edge degree at most one on DDT as 98.24%, the sum of the
  rounded 84.95% and 13.29%; [the counts give 98.25%](##edgeDegree_atMost_one_ddt).
* The text gives the 7 structures of DDT at gap degree 2 as 0.17%; they are 0.16%, as Table 1
  prints.

## References

* [kuhlmann-nivre-2006]
* [nivre-2006]
-/

@[expose] public section

namespace KuhlmannNivre2006

open DependencyGrammar Relation
open Morphology (Word)

variable {L : Type*} {n : ℕ} (g : Graph L n)

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
  g.arcs.sup fun p ↦ edgeDegreeAt g p.1 p.2

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
  simp only [Graph.mem_arcs, Nat.bot_eq_zero, Prod.forall, edgeDegreeAt_eq_zero_iff hT]
  exact Iff.rfl

/-! ### Figure 1: a dependency forest

The analysis of *Není proto zapotřebí uzavírat nové nájemní smlouvy.* leaves *proto* and the final
punctuation mark without a head, so it is a forest and not a tree, and the yield of *není* skips
*proto*. -/

/-- An unlabelled position. -/
def dot : Word := Word.mk' "•" .X

/-- Figure 1: nodes 2 and 8 have no head. -/
def fig1 : Graph Unit 8 :=
  .ofArcs [dot, dot, dot, dot, dot, dot, dot, dot] 1
    [(1, 0, ()), (0, 2, ()), (0, 3, ()), (3, 6, ()), (6, 4, ()), (6, 5, ())]

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
def fig2a : Graph Unit 3 := .ofArcs [dot, dot, dot] 1 [(1, 0, ()), (0, 2, ())]

/-- Figure 2b: the edges (1, 4) and (3, 5) cross. -/
def fig2b : Graph Unit 5 :=
  .ofArcs [dot, dot, dot, dot, dot] 1 [(1, 0, ()), (0, 3, ()), (3, 2, ()), (2, 4, ())]

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
def fig3a : Graph Unit 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, ()), (1, 2, ()), (2, 3, ()), (0, 4, ()), (4, 5, ())]

/-- Figure 3b: the projection of node 2 is `(2, 3, 6)`, with the gap `(3, 6)`. -/
def fig3b : Graph Unit 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, ()), (1, 2, ()), (2, 5, ()), (0, 3, ()), (3, 4, ())]

/-- Figure 3c: the projection of node 2 is `(2, 4, 6)`, with the gaps `(2, 4)` and `(4, 6)`. -/
def fig3c : Graph Unit 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, ()), (1, 3, ()), (3, 5, ()), (0, 2, ()), (2, 4, ())]

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
def fig4a : Graph Unit 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, ()), (0, 2, ()), (2, 4, ()), (1, 3, ()), (3, 5, ())]

/-- Figure 4b: the subtree at node 2 has one gap, containing two components node 2 does not
dominate. -/
def fig4b : Graph Unit 5 :=
  .ofArcs [dot, dot, dot, dot, dot] 0 [(0, 1, ()), (0, 2, ()), (0, 3, ()), (1, 4, ())]

theorem figure4_isTree : fig4a.IsTree ∧ fig4b.IsTree := by decide

-- Figure 4
theorem figure4_degrees :
    (fig4a.gapDegreeAt 1 = 2 ∧ fig4a.gapDegree = 2 ∧ edgeDegree fig4a = 1) ∧
      (fig4b.gapDegreeAt 1 = 1 ∧ fig4b.gapDegree = 1 ∧ edgeDegreeAt fig4b 1 4 = 2 ∧
        edgeDegree fig4b = 2) := by
  decide +kernel

/-! ### Table 1: the constraints on the Danish and Prague treebanks

The rows at degree zero and the rows over the non-projective structures follow from the counts
over all structures, through the degree-zero theorems and the hierarchy. -/

open Data.Statistics (Decimal)

/-- What a binary constraint says of a graph. -/
def Constraint.Holds : Constraint → Graph L n → Prop
  | .planar, g => g.IsPlanar
  | .wellNested, g => g.IsWellNested

instance : ∀ (c : Constraint) (g : Graph L n), Decidable (c.Holds g)
  | .planar, g => inferInstanceAs (Decidable g.IsPlanar)
  | .wellNested, g => inferInstanceAs (Decidable g.IsWellNested)

/-- The degree a graded measure gives a graph. -/
def Measure.degree : Measure → Graph L n → ℕ
  | .gap, g => g.gapDegree
  | .edge, g => edgeDegree g

theorem Measure.degree_eq_zero_iff (hT : g.IsTree) {m : Measure} :
    m.degree g = 0 ↔ g.IsProjective := by
  cases m
  exacts [Graph.isProjective_iff_gapDegree_eq_zero.symm, edgeDegree_eq_zero_iff hT]

/-- The number of structures of `t` at degree `d` on `m`, zero at a dash or past the table. -/
def count (m : Measure) (t : Treebank) (d : ℕ) : ℕ := ((degrees m t).counts.getD d none).getD 0

/-- The number of structures of `t` of degree at most `k` on `m`. -/
def atMost (m : Measure) (t : Treebank) (k : ℕ) : ℕ := ∑ d ∈ Finset.range (k + 1), count m t d

theorem atMost_mono (m : Measure) (t : Treebank) : Monotone (atMost m t) := fun _ _ h ↦
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.succ_le_succ h))

variable {T : Multiset (Σ n, Graph L n)} {t : Treebank}

/-- A treebank has the counts Table 1 prints for `t` over all of its structures. -/
structure HasCounts (T : Multiset (Σ n, Graph L n)) (t : Treebank) : Prop where
  card_eq : Multiset.card T = (structures t).all
  countP_isProjective : T.countP (·.2.IsProjective) = (structures t).projective
  countP_holds (c : Constraint) : T.countP (c.Holds ·.2) = (coverage c t).all

private theorem countP_replicate {α : Type*} (p : α → Prop) [DecidablePred p] (a : α) (k : ℕ) :
    (Multiset.replicate k a).countP p = if p a then k else 0 := by
  rw [← Multiset.coe_replicate, Multiset.coe_countP, List.countP_replicate]
  simp

/-- Copies of the trees of Figures 2a, 3a, 3b and 3c make a treebank with the counts of Table 1,
which is thus not vacuous. -/
theorem exists_hasCounts (t : Treebank) :
    ∃ T : Multiset (Σ n, Graph Unit n), (∀ g ∈ T, g.2.IsTree) ∧ HasCounts T t := by
  have h3a : fig3a.IsProjective ∧ fig3a.IsPlanar ∧ fig3a.IsWellNested := by decide +kernel
  have h2a : ¬ fig2a.IsProjective ∧ fig2a.IsPlanar ∧ fig2a.IsWellNested := by decide +kernel
  have h3b : ¬ fig3b.IsProjective ∧ ¬ fig3b.IsPlanar ∧ fig3b.IsWellNested := by decide +kernel
  have h3c : ¬ fig3c.IsProjective ∧ ¬ fig3c.IsPlanar ∧ ¬ fig3c.IsWellNested := by
    decide +kernel
  refine ⟨.replicate (structures t).projective ⟨6, fig3a⟩ +
    .replicate ((coverage .planar t).all - (structures t).projective) ⟨3, fig2a⟩ +
    .replicate ((coverage .wellNested t).all - (coverage .planar t).all) ⟨6, fig3b⟩ +
    .replicate ((structures t).all - (coverage .wellNested t).all) ⟨6, fig3c⟩, ?_, ?_, ?_, ?_⟩
  · simp only [Multiset.mem_add, Multiset.mem_replicate]
    rintro g (((⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩)
    exacts [figure3_isTree.1, fig2a_isTree, figure3_isTree.2.1, figure3_isTree.2.2]
  · simp only [Multiset.card_add, Multiset.card_replicate]
    cases t <;> decide
  · simp only [Multiset.countP_add, countP_replicate, h3a, h2a, h3b, h3c, ↓reduceIte, add_zero]
  · intro c
    simp only [Multiset.countP_add, countP_replicate]
    cases c <;> simp only [Constraint.Holds, h3a, h2a, h3b, h3c, ↓reduceIte, add_zero] <;>
      cases t <;> decide

/-- Over a treebank of trees with the counts of Table 1, the structures at degree zero on either
measure are as many as the table prints. -/
theorem HasCounts.countP_degree_eq_zero (h : HasCounts T t) (hT : ∀ g ∈ T, g.2.IsTree)
    (m : Measure) : T.countP (m.degree ·.2 = 0) = count m t 0 := by
  rw [Multiset.countP_congr rfl fun g hg ↦ propext (Measure.degree_eq_zero_iff (hT g hg)),
    h.countP_isProjective]
  clear h hT
  revert m t
  decide

/-- Over a treebank of forests with the counts of Table 1, the non-projective structures, and
those of them meeting each binary constraint, are as many as the table prints. -/
theorem HasCounts.countP_nonProjective (h : HasCounts T t) (hF : ∀ g ∈ T, g.2.IsForest) :
    T.countP (¬ ·.2.IsProjective) = (structures t).nonProjective ∧
      ∀ c : Constraint, T.countP (fun g ↦ c.Holds g.2 ∧ ¬ g.2.IsProjective) =
        (coverage c t).nonProjective := by
  have hs : ∀ t, (structures t).nonProjective + (structures t).projective = (structures t).all ∧
      ∀ c, (coverage c t).nonProjective + (structures t).projective = (coverage c t).all := by
    decide
  refine ⟨?_, fun c ↦ ?_⟩
  · have hp := Multiset.card_eq_countP_add_countP (·.2.IsProjective) T
    rw [h.card_eq, h.countP_isProjective] at hp
    have := (hs t).1
    omega
  · have hc := Multiset.countP_eq_countP_filter_add T (c.Holds ·.2) (·.2.IsProjective)
    rw [Multiset.countP_filter, Multiset.countP_filter, Multiset.countP_congr rfl fun g hg ↦
      propext (and_iff_right_of_imp fun hP ↦ ?_), h.countP_holds, h.countP_isProjective] at hc
    · have := (hs t).2 c
      omega
    · cases c
      exacts [hP.isPlanar (hF g hg), hP.isWellNested (hF g hg)]

-- p. 512, p. 513
theorem nonProjective_share :
    (⟨15, 0⟩ : Decimal).RoundsPercent (structures .ddt).nonProjective (structures .ddt).all ∧
      (⟨23, 0⟩ : Decimal).RoundsPercent (structures .pdt).nonProjective (structures .pdt).all := by
  decide

/-- The least degree covering every structure is 2 on gap degree and 4 on edge degree for DDT,
and 4 and 6 for PDT. -/
theorem isLeast_atMost_eq_all :
    IsLeast {k | atMost .gap .ddt k = (structures .ddt).all} 2 ∧
      IsLeast {k | atMost .edge .ddt k = (structures .ddt).all} 4 ∧
        IsLeast {k | atMost .gap .pdt k = (structures .pdt).all} 4 ∧
          IsLeast {k | atMost .edge .pdt k = (structures .pdt).all} 6 := by
  have key {m t} (k : ℕ) (h : atMost m t (k + 1) = (structures t).all)
      (h' : atMost m t k < (structures t).all) :
      IsLeast {j | atMost m t j = (structures t).all} (k + 1) :=
    ⟨h, fun j hj ↦ le_of_not_gt fun hj' ↦
      ((atMost_mono m t (Nat.le_of_lt_succ hj')).trans_lt h').ne hj⟩
  refine ⟨key 1 ?_ ?_, key 3 ?_ ?_, key 3 ?_ ?_, key 5 ?_ ?_⟩ <;> decide

-- p. 513
theorem atMost_one_share :
    (⟨9825, 2⟩ : Decimal).RoundsPercent (atMost .edge .ddt 1) (structures .ddt).all ∧
      (⟨9954, 2⟩ : Decimal).RoundsPercent (atMost .edge .pdt 1) (structures .pdt).all ∧
        (⟨9984, 2⟩ : Decimal).RoundsPercent (atMost .gap .ddt 1) (structures .ddt).all ∧
          (⟨9957, 2⟩ : Decimal).RoundsPercent (atMost .gap .pdt 1) (structures .pdt).all := by
  decide

-- p. 513
theorem edgeDegree_atMost_one_ddt :
    ¬ (⟨9824, 2⟩ : Decimal).RoundsPercent (atMost .edge .ddt 1) (structures .ddt).all ∧
      (⟨8495, 2⟩ : Decimal).RoundsPercent (count .edge .ddt 0) (structures .ddt).all ∧
        (⟨1329, 2⟩ : Decimal).RoundsPercent (count .edge .ddt 1) (structures .ddt).all ∧
          (⟨8495, 2⟩ : Decimal).toRat + (⟨1329, 2⟩ : Decimal).toRat =
            (⟨9824, 2⟩ : Decimal).toRat := by
  decide +kernel

-- p. 512
theorem gapDegree_two_ddt :
    ¬ (⟨17, 2⟩ : Decimal).RoundsPercent (count .gap .ddt 2) (structures .ddt).all ∧
      (⟨16, 2⟩ : Decimal).RoundsPercent (count .gap .ddt 2) (structures .ddt).all := by
  decide

-- p. 512, p. 513
theorem planar_share :
    (⟨8641, 2⟩ : Decimal).RoundsPercent (coverage .planar .ddt).all (structures .ddt).all ∧
      (⟨8216, 2⟩ : Decimal).RoundsPercent (coverage .planar .pdt).all (structures .pdt).all ∧
        ((coverage .planar .ddt).nonProjective : ℚ) / (structures .ddt).nonProjective < 1 / 10 ∧
          (⟨2293, 2⟩ : Decimal).RoundsPercent (coverage .planar .pdt).nonProjective
            (structures .pdt).nonProjective := by
  decide +kernel

-- p. 512, p. 513
theorem wellNested_share :
    (⟨9989, 2⟩ : Decimal).RoundsPercent (coverage .wellNested .ddt).all (structures .ddt).all ∧
      (⟨9989, 2⟩ : Decimal).RoundsPercent (coverage .wellNested .pdt).all (structures .pdt).all ∧
        99 / 100 < ((coverage .wellNested .ddt).nonProjective : ℚ) /
          (structures .ddt).nonProjective := by
  decide +kernel

end KuhlmannNivre2006
