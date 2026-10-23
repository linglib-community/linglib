module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset

/-!
# Maximal independent sets of a finite graph

`[UPSTREAM]` candidate for `Mathlib/Combinatorics/SimpleGraph/Clique.lean`. A set of vertices is
a maximal independent set exactly when it is independent and every vertex outside it is adjacent
to one inside. For a finset of vertices of a finite graph this is decidable, so the maximal
independent sets form a computable finset.

## Main definitions

* `SimpleGraph.maximalIndepSets`: the finset of maximal independent sets of a finite graph.

## Main statements

* `SimpleGraph.maximal_isIndepSet_iff_forall_exists_adj`: a set is a maximal independent set
  exactly when it is independent and dominating.
* `SimpleGraph.mem_maximalIndepSets`: membership in `maximalIndepSets` is `Maximal
  G.IsIndepSet`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

theorem maximal_isIndepSet_iff_forall_exists_adj {s : Set V} :
    Maximal G.IsIndepSet s ↔ G.IsIndepSet s ∧ ∀ v ∉ s, ∃ w ∈ s, G.Adj v w := by
  rw [Set.maximal_iff_forall_insert fun _ _ ht hst ↦ ht.mono hst]
  refine and_congr_right fun hs ↦ forall₂_congr fun v hv ↦ ?_
  simp [IsIndepSet, Set.pairwise_insert_of_notMem hv, hs, G.adj_comm]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s : Finset V}

/-- The maximal independent sets of a finite graph. -/
def maximalIndepSets : Finset (Finset V) :=
  {s | G.IsIndepSet ↑s ∧ ∀ v ∉ s, ∃ w ∈ s, G.Adj v w}

@[simp] theorem mem_maximalIndepSets : s ∈ G.maximalIndepSets ↔ Maximal G.IsIndepSet ↑s := by
  simp [maximalIndepSets, maximal_isIndepSet_iff_forall_exists_adj]

end SimpleGraph
