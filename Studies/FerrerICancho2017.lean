module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Basic
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Syntax.WordOrder.Projectivity
public import Linglib.Syntax.WordOrder.ArcLength
public import Linglib.Core.Combinatorics.SimpleGraph.Crossings

/-!
# Ferrer-i-Cancho (2017): Random crossings in dependency trees

Ferrer-i-Cancho asks how many crossings a sentence would show if its word order were lost and
replaced by a uniformly random one. Two links cross in a third of the linearizations when they
share no word and in none otherwise, so a random linearization
[expects a third](##FerrerICancho2017.three_mul_sum_crossings_comap) of the potential crossings
$C_{pairs}$, the number of pairs of links sharing no word, which
[bounds the crossings](##FerrerICancho2017.crossings_comap_le_disjointEdgePairs) of every
linearization. Potential crossings are all pairs of links
[but those meeting at a word](##SimpleGraph.disjointEdgePairs_add_sum_choose_degree), so in
a tree the sentence length $n$ and the second moment $⟨k^2⟩$ of the degrees
[fix them](##FerrerICancho2017.two_mul_disjointEdgePairs_add_sum_degree_sq_of_isArborescence),
and the [expected number of
crossings](##FerrerICancho2017.six_mul_sum_crossings_comap_add_of_isArborescence)
is $n (n - 1 - ⟨k^2⟩) / 6$. It vanishes for a star tree, where
[no linearization has a
crossing](##FerrerICancho2017.crossings_comap_eq_zero_of_forall_symmGen), and
is [greatest](##FerrerICancho2017.six_mul_sum_crossings_comap_le_of_isArborescence) for a
[linear tree](##FerrerICancho2017.six_mul_sum_crossings_comap_of_degree_le_two), at
$(n - 2) (n - 3) / 6$.

## Implementation notes

* The paper neglects the direction of a dependency, and its results are those of
  `Linglib/Core/Combinatorics/SimpleGraph/Crossings.lean` on the undirected view of a dependency
  graph. `Digraph.crossings` is the crossings of that view, and its relabellings are the
  linearizations of the graph (`Digraph.toSimpleGraphInclusive_map`). $C_{pairs}$ is
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

open DependencyGrammar Finset Equiv Nat Relation

variable {n : ℕ} {G : Digraph (Fin n)} [DecidableRel G.Adj]

/-! ### The undirected view -/

theorem sum_crossings_comap :
    ∑ σ : Perm (Fin n), (G.comap σ.symm).crossings =
      ∑ σ : Perm (Fin n), (G.toSimpleGraphInclusive.comap σ).crossings := by
  simp only [Digraph.crossings_comap (Equiv.injective _)]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun _ ↦ rfl

-- relinearizing preserves the tree, and so the second moment of the degrees
theorem sum_degree_sq_comap (σ : Perm (Fin n)) :
    ∑ v, (G.comap σ.symm).toSimpleGraphInclusive.degree v ^ 2 =
      ∑ v, G.toSimpleGraphInclusive.degree v ^ 2 := by
  convert G.toSimpleGraphInclusive.sum_degree_sq_comap σ.symm using 4
  exact Digraph.toSimpleGraphInclusive_comap σ.symm.injective G

/-! ### Expected crossings and potential crossings -/

/-- Summed over all `n !` linearizations, three times the crossing count is `n !` times the number
of pairs of links sharing no word ([ferrer-i-cancho-2017], eq. 13). -/
theorem three_mul_sum_crossings_comap :
    3 * ∑ σ : Perm (Fin n), (G.comap σ.symm).crossings = n ! *
      G.toSimpleGraphInclusive.disjointEdgePairs := by
  rw [sum_crossings_comap, SimpleGraph.three_mul_sum_crossings_comap, Fintype.card_fin]

-- no linearization has more crossings than there are pairs of links sharing no word
theorem crossings_comap_le_disjointEdgePairs (σ : Perm (Fin n)) :
    (G.comap σ.symm).crossings ≤ G.toSimpleGraphInclusive.disjointEdgePairs :=
  (Digraph.crossings_comap σ.symm.injective).trans_le
    (SimpleGraph.crossings_comap_le_disjointEdgePairs _)

/-- When every link meets one word, as in a star tree, no linearization has a crossing
([ferrer-i-cancho-2017], after eq. 14). -/
theorem crossings_comap_eq_zero_of_forall_symmGen {h : Fin n}
    (hh : ∀ ⦃a b⦄, SymmGen G.Adj a b → a = h ∨ b = h) (σ : Perm (Fin n)) :
    (G.comap σ.symm).crossings = 0 :=
  Nat.eq_zero_of_le_zero <| (crossings_comap_le_disjointEdgePairs σ).trans_eq <|
    SimpleGraph.disjointEdgePairs_eq_zero_of_forall_adj fun _ _ hab ↦ hh hab.2

/-! ### Trees -/

/-- A tree has `n (n - 1 - ⟨k²⟩) / 2` pairs of links sharing no word ([ferrer-i-cancho-2017],
eq. 3, from [ferrer-i-cancho-2013]). -/
theorem two_mul_disjointEdgePairs_add_sum_degree_sq_of_isArborescence {r : Fin n}
    (hT : G.IsArborescence r) :
    2 * G.toSimpleGraphInclusive.disjointEdgePairs + ∑ v, G.toSimpleGraphInclusive.degree v ^ 2 = n
      * (n - 1) := by
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.two_mul_disjointEdgePairs_add_sum_degree_sq hT.isTree_toSimpleGraphInclusive

/-- A uniformly random linearization of a tree expects `n (n - 1 - ⟨k²⟩) / 6` crossings
([ferrer-i-cancho-2017], eq. 14). -/
theorem six_mul_sum_crossings_comap_add_of_isArborescence {r : Fin n} (hT : G.IsArborescence r) :
    6 * ∑ σ : Perm (Fin n), (G.comap σ.symm).crossings +
        n ! * ∑ v, G.toSimpleGraphInclusive.degree v ^ 2 =
      n ! * (n * (n - 1)) := by
  rw [sum_crossings_comap]
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.six_mul_sum_crossings_comap_add hT.isTree_toSimpleGraphInclusive

-- eq. 16, upper bound
theorem sum_degree_sq_le_of_isArborescence {r : Fin n} (hT : G.IsArborescence r) :
    ∑ v, G.toSimpleGraphInclusive.degree v ^ 2 ≤ n * (n - 1) := by
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.sum_degree_sq_le hT.isTree_toSimpleGraphInclusive

-- eq. 16, lower bound
theorem le_sum_degree_sq_of_isArborescence {r : Fin n} (hT : G.IsArborescence r) :
    4 * n - 6 ≤ ∑ v, G.toSimpleGraphInclusive.degree v ^ 2 := by
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.le_sum_degree_sq hT.isTree_toSimpleGraphInclusive

/-- A uniformly random linearization of a tree expects at most `(n - 2) (n - 3) / 6` crossings
([ferrer-i-cancho-2017], eq. 17). -/
theorem six_mul_sum_crossings_comap_le_of_isArborescence {r : Fin n} (hT : G.IsArborescence r) :
    6 * ∑ σ : Perm (Fin n), (G.comap σ.symm).crossings ≤ n ! * ((n - 2) * (n - 3)) := by
  rw [sum_crossings_comap]
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.six_mul_sum_crossings_comap_le hT.isTree_toSimpleGraphInclusive

-- eq. 15
theorem six_mul_sum_crossings_comap_of_degree_le_two {r : Fin n} (hT : G.IsArborescence r)
    (h2 : ∀ v, G.toSimpleGraphInclusive.degree v ≤ 2) :
    6 * ∑ σ : Perm (Fin n), (G.comap σ.symm).crossings = n ! * ((n - 2) * (n - 3)) := by
  rw [sum_crossings_comap]
  simpa only [Fintype.card_fin] using
    SimpleGraph.IsTree.six_mul_sum_crossings_comap_of_degree_le_two
      hT.isTree_toSimpleGraphInclusive h2

-- the linear tree on four words: one potential crossing, a third of a crossing expected
example {G : Digraph (Fin 4)} [DecidableRel G.Adj] {r : Fin 4} (hT : G.IsArborescence r)
    (h2 : ∀ v, G.toSimpleGraphInclusive.degree v ≤ 2) :
    3 * ∑ σ : Perm (Fin 4), (G.comap σ.symm).crossings = 4 ! := by
  have h := six_mul_sum_crossings_comap_of_degree_le_two hT h2
  have h4 : (4 : ℕ)! = 24 := rfl
  omega

/-! ### The paper's examples -/

/-- Fig. 1: *She loved me for the dangers I had passed* in [melcuk-1988]'s analysis, where the
preposition heads its object and the auxiliary heads the relative clause. Relations other than
the subject and object of *loved*, which the caption names, are `dep`. -/
def fig1 : Graph UD.DepRel (Fin 9) :=
  .ofArcs [(1, 0, .nsubj), (1, 2, .obj), (1, 3, .dep), (3, 5, .dep), (5, 4, .dep), (5, 7, .dep),
    (7, 6, .dep), (7, 8, .dep)]

theorem fig1_isArborescence : fig1.IsArborescence 1 := by decide

-- Fig. 1: the sentence in its own order has no crossing
theorem fig1_crossings : fig1.crossings = 0 := by decide +kernel

-- Fig. 1: mean dependency length 11 / 8
theorem fig1_totalLength : fig1.totalLength = 11 := by decide +kernel

/-- Fig. 2: the order *loved had me for dangers I she the passed*, as the position each word of
Fig. 1 moves to. -/
def fig2 : Perm (Fin 9) :=
  ⟨![6, 0, 2, 3, 7, 4, 5, 1, 8], ![1, 7, 2, 3, 5, 6, 0, 4, 8], by decide, by decide⟩

-- Fig. 2
theorem fig2_crossings : (fig1.toDigraph.comap fig2.symm).crossings = 9 := by decide +kernel

-- Fig. 1
theorem fig1_sum_degree_sq : ∑ v, fig1.toSimpleGraphInclusive.degree v ^ 2 = 36 := by decide

-- Fig. 1
theorem fig1_disjointEdgePairs : fig1.toSimpleGraphInclusive.disjointEdgePairs = 18 := by
  have h := two_mul_disjointEdgePairs_add_sum_degree_sq_of_isArborescence fig1_isArborescence
  rw [fig1_sum_degree_sq] at h
  omega

-- Fig. 1 expects six crossings under a random linearization, the value after eq. 14
theorem fig1_sum_crossings_comap :
    ∑ σ : Perm (Fin 9), (fig1.toDigraph.comap σ.symm).crossings = 6 * 9 ! := by
  have h := six_mul_sum_crossings_comap_add_of_isArborescence fig1_isArborescence
  rw [fig1_sum_degree_sq] at h
  omega

end FerrerICancho2017
