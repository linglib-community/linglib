module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Core.Combinatorics.SimpleGraph.Crossings

/-!
# Ferrer-i-Cancho (2017): Random crossings in dependency trees

Ferrer-i-Cancho asks how many crossings a sentence would show if its word order were lost and
replaced by a uniformly random one. Two links cross in a third of the linearizations when they
share no word and in none otherwise, so a random linearization
[expects a third](##FerrerICancho2017.three_mul_sum_crossings_map) of the potential crossings
$C_{pairs}$, the number of pairs of links sharing no word, which
[bounds the crossings](##FerrerICancho2017.crossings_map_le_disjointEdgePairs) of every
linearization. Potential crossings are all pairs of links
[but those meeting at a word](##SimpleGraph.disjointEdgePairs_add_sum_choose_degree), so in
a tree the sentence length $n$ and the second moment $⟨k^2⟩$ of the degrees
[fix them](##FerrerICancho2017.two_mul_disjointEdgePairs_add_sum_degree_sq_of_isTree), and the
[expected number of crossings](##FerrerICancho2017.six_mul_sum_crossings_map_add_of_isTree)
is $n (n - 1 - ⟨k^2⟩) / 6$. It vanishes for a star tree, where
[no linearization has a crossing](##FerrerICancho2017.crossings_map_eq_zero_of_forall_linked), and
is [greatest](##FerrerICancho2017.six_mul_sum_crossings_map_le_of_isTree) for a
[linear tree](##FerrerICancho2017.six_mul_sum_crossings_map_of_degree_le_two), at
$(n - 2) (n - 3) / 6$.

## Implementation notes

* The paper neglects the direction of a dependency, and its results are those of
  `Linglib/Core/Combinatorics/SimpleGraph/Crossings.lean` on the undirected view of a dependency
  graph, whose [crossings](##FerrerICancho2017.crossings_eq) are the graph's and whose
  [relabellings](##FerrerICancho2017.toSimpleGraph_map) are its linearizations. $C_{pairs}$ is
  `SimpleGraph.disjointEdgePairs` of that view.
* Expectations are stated as counts over all $n!$ linearizations, with the divisions cleared, and
  the second moment as the sum $∑ k^2 = n ⟨k^2⟩$.
* The greatest expected number of crossings is stated as $(n - 2) (n - 3) / 6$, which equals the
  paper's $n (n - 5) / 6 + 1$.

## TODO

* The uniqueness of the star and the linear tree as the extremes of $⟨k^2⟩$.
* The expected dependency length $(n + 1) / 3$ of a random linearization.

## References

* [ferrer-i-cancho-2017]
* [ferrer-i-cancho-2013]
* [melcuk-1988]
-/

@[expose] public section

namespace FerrerICancho2017

open DependencyGrammar Finset Equiv Nat

variable {L : Type*} {n : ℕ} {g : Graph L n}

/-! ### The undirected view -/

theorem crossings_eq : g.crossings = g.toSimpleGraph.crossings := by
  unfold Graph.crossings SimpleGraph.crossings
  refine congrArg card (filter_congr fun x _ ↦ ?_)
  simp only [Graph.toSimpleGraph_adj]
  exact ⟨fun ⟨h1, h2, hac, hcb, hbd⟩ ↦
      ⟨⟨(hac.trans hcb).ne, h1⟩, ⟨(hcb.trans hbd).ne, h2⟩, hac, hcb, hbd⟩,
    fun ⟨h1, h2, h⟩ ↦ ⟨h1.2, h2.2, h⟩⟩

theorem toSimpleGraph_map (σ : Perm (Fin n)) :
    (g.map σ).toSimpleGraph = g.toSimpleGraph.comap σ.symm := by
  ext v w
  simp

theorem crossings_map (σ : Perm (Fin n)) :
    (g.map σ).crossings = (g.toSimpleGraph.comap σ.symm).crossings := by
  rw [crossings_eq]
  unfold SimpleGraph.crossings
  refine congrArg card (filter_congr fun x _ ↦ ?_)
  simp

theorem sum_crossings_map :
    ∑ σ : Perm (Fin n), (g.map σ).crossings =
      ∑ σ : Perm (Fin n), (g.toSimpleGraph.comap σ).crossings := by
  simp only [crossings_map]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun _ ↦ rfl

-- relinearizing preserves the tree, and so the second moment of the degrees
theorem sum_degree_sq_map (σ : Perm (Fin n)) :
    ∑ v, (g.map σ).toSimpleGraph.degree v ^ 2 = ∑ v, g.toSimpleGraph.degree v ^ 2 := by
  convert g.toSimpleGraph.sum_degree_sq_comap σ.symm using 4
  exact toSimpleGraph_map σ

/-! ### Expected crossings and potential crossings -/

/-- Summed over all `n !` linearizations, three times the crossing count is `n !` times the number
of pairs of links sharing no word ([ferrer-i-cancho-2017], eq. 13). -/
theorem three_mul_sum_crossings_map :
    3 * ∑ σ : Perm (Fin n), (g.map σ).crossings = n ! * g.toSimpleGraph.disjointEdgePairs := by
  rw [sum_crossings_map, SimpleGraph.three_mul_sum_crossings_comap, Fintype.card_fin]

-- no linearization has more crossings than there are pairs of links sharing no word
theorem crossings_map_le_disjointEdgePairs (σ : Perm (Fin n)) :
    (g.map σ).crossings ≤ g.toSimpleGraph.disjointEdgePairs :=
  (crossings_map σ).trans_le (SimpleGraph.crossings_comap_le_disjointEdgePairs _)

/-- When every link meets one word, as in a star tree, no linearization has a crossing
([ferrer-i-cancho-2017], after eq. 14). -/
theorem crossings_map_eq_zero_of_forall_linked {h : Fin n}
    (hh : ∀ ⦃a b⦄, g.Linked a b → a = h ∨ b = h) (σ : Perm (Fin n)) :
    (g.map σ).crossings = 0 :=
  Nat.eq_zero_of_le_zero <| (crossings_map_le_disjointEdgePairs σ).trans_eq <|
    SimpleGraph.disjointEdgePairs_eq_zero_of_forall_adj fun _ _ hab ↦ hh hab.2

/-! ### Trees -/

/-- A tree has `n (n - 1 - ⟨k²⟩) / 2` pairs of links sharing no word ([ferrer-i-cancho-2017],
eq. 3, from [ferrer-i-cancho-2013]). -/
theorem two_mul_disjointEdgePairs_add_sum_degree_sq_of_isTree (hT : g.IsTree) :
    2 * g.toSimpleGraph.disjointEdgePairs + ∑ v, g.toSimpleGraph.degree v ^ 2 = n * (n - 1) := by
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.two_mul_disjointEdgePairs_add_sum_degree_sq hT.isTree_toSimpleGraph

/-- A uniformly random linearization of a tree expects `n (n - 1 - ⟨k²⟩) / 6` crossings
([ferrer-i-cancho-2017], eq. 14). -/
theorem six_mul_sum_crossings_map_add_of_isTree (hT : g.IsTree) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings + n ! * ∑ v, g.toSimpleGraph.degree v ^ 2 =
      n ! * (n * (n - 1)) := by
  rw [sum_crossings_map]
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.six_mul_sum_crossings_comap_add hT.isTree_toSimpleGraph

-- eq. 16, upper bound
theorem sum_degree_sq_le_of_isTree (hT : g.IsTree) :
    ∑ v, g.toSimpleGraph.degree v ^ 2 ≤ n * (n - 1) := by
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.sum_degree_sq_le hT.isTree_toSimpleGraph

-- eq. 16, lower bound
theorem le_sum_degree_sq_of_isTree (hT : g.IsTree) :
    4 * n - 6 ≤ ∑ v, g.toSimpleGraph.degree v ^ 2 := by
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.le_sum_degree_sq hT.isTree_toSimpleGraph

/-- A uniformly random linearization of a tree expects at most `(n - 2) (n - 3) / 6` crossings
([ferrer-i-cancho-2017], eq. 17). -/
theorem six_mul_sum_crossings_map_le_of_isTree (hT : g.IsTree) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings ≤ n ! * ((n - 2) * (n - 3)) := by
  rw [sum_crossings_map]
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.six_mul_sum_crossings_comap_le hT.isTree_toSimpleGraph

-- eq. 15
theorem six_mul_sum_crossings_map_of_degree_le_two (hT : g.IsTree)
    (h2 : ∀ v, g.toSimpleGraph.degree v ≤ 2) :
    6 * ∑ σ : Perm (Fin n), (g.map σ).crossings = n ! * ((n - 2) * (n - 3)) := by
  rw [sum_crossings_map]
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.six_mul_sum_crossings_comap_of_degree_le_two hT.isTree_toSimpleGraph h2

-- the linear tree on four words: one potential crossing, a third of a crossing expected
example {g : Graph L 4} (hT : g.IsTree) (h2 : ∀ v, g.toSimpleGraph.degree v ≤ 2) :
    3 * ∑ σ : Perm (Fin 4), (g.map σ).crossings = 4 ! := by
  have h := six_mul_sum_crossings_map_of_degree_le_two hT h2
  have h4 : (4 : ℕ)! = 24 := rfl
  omega

/-! ### The paper's examples -/

/-- Fig. 1: *She loved me for the dangers I had passed* in [melcuk-1988]'s analysis, where the
preposition heads its object and the auxiliary heads the relative clause. Relations other than
the subject and object of *loved*, which the caption names, are `dep`. -/
def fig1 : Tree UD.DepRel 9 :=
  .mk' (.ofArcs 1 [(1, 0, .nsubj), (1, 2, .obj), (1, 3, .dep), (3, 5, .dep), (5, 4, .dep),
      (5, 7, .dep),
      (7, 6, .dep), (7, 8, .dep)])

-- Fig. 1: the sentence in its own order has no crossing
theorem fig1_crossings : fig1.toGraph.crossings = 0 := by decide +kernel

-- Fig. 1: mean dependency length 11 / 8
theorem fig1_totalLength : fig1.toGraph.totalLength = 11 := by decide +kernel

/-- Fig. 2: the order *loved had me for dangers I she the passed*, as the position each word of
Fig. 1 moves to. -/
def fig2 : Perm (Fin 9) :=
  ⟨![6, 0, 2, 3, 7, 4, 5, 1, 8], ![1, 7, 2, 3, 5, 6, 0, 4, 8], by decide, by decide⟩

-- Fig. 2
theorem fig2_crossings : (fig1.toGraph.map fig2).crossings = 9 := by decide +kernel

-- Fig. 1
theorem fig1_sum_degree_sq : ∑ v, fig1.toGraph.toSimpleGraph.degree v ^ 2 = 36 := by decide

-- Fig. 1
theorem fig1_disjointEdgePairs : fig1.toGraph.toSimpleGraph.disjointEdgePairs = 18 := by
  have h := two_mul_disjointEdgePairs_add_sum_degree_sq_of_isTree fig1.isTree
  rw [fig1_sum_degree_sq] at h
  omega

-- Fig. 1 expects six crossings under a random linearization, the value after eq. 14
theorem fig1_sum_crossings_map :
    ∑ σ : Perm (Fin 9), (fig1.toGraph.map σ).crossings = 6 * 9 ! := by
  have h := six_mul_sum_crossings_map_add_of_isTree fig1.isTree
  rw [fig1_sum_degree_sq] at h
  omega

end FerrerICancho2017
