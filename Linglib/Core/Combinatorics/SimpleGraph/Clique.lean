module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset

/-!
# Maximal independent sets

`[UPSTREAM]` candidate for `Mathlib/Combinatorics/SimpleGraph/Clique.lean`. Adding a vertex to an
independent set [keeps it independent](##SimpleGraph.isIndepSet_insert) exactly when the vertex
has no neighbour in the set, so a set is a maximal independent set exactly when it is
[independent and dominating](##SimpleGraph.isMaximalIndepSet_iff_forall_exists_adj). This decides
maximality for a finset of vertices of a finite graph, whose maximal independent sets then form
the finset `SimpleGraph.maximalIndepSets`, an
[antichain](##SimpleGraph.isAntichain_maximalIndepSets).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s t : Set V} {a : V}

theorem IsIndepSet.subset (h : t ⊆ s) : G.IsIndepSet s → G.IsIndepSet t := Set.Pairwise.mono h

@[simp]
theorem isIndepSet_insert : G.IsIndepSet (insert a s) ↔ G.IsIndepSet s ∧ ∀ b ∈ s, ¬G.Adj a b := by
  have : Std.Symm fun v w ↦ ¬G.Adj v w := ⟨fun _ _ h h' ↦ h h'.symm⟩
  exact Set.pairwise_insert_of_symm.trans <| and_congr_right fun _ ↦
    forall₂_congr fun _ _ ↦ ⟨fun h hab ↦ h hab.ne hab, fun h _ ↦ h⟩

/-- A set of vertices is a maximal independent set exactly when it is independent and every
vertex outside it is adjacent to one inside. -/
theorem isMaximalIndepSet_iff_forall_exists_adj :
    Maximal G.IsIndepSet s ↔ G.IsIndepSet s ∧ ∀ v ∉ s, ∃ w ∈ s, G.Adj v w := by
  rw [Set.maximal_iff_forall_insert fun _ _ ht hst ↦ ht.subset hst]
  exact and_congr_right fun hs ↦ by simp [hs]

variable (G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s t : Finset V}

instance : Decidable (Maximal G.IsIndepSet (s : Set V)) :=
  decidable_of_iff (G.IsIndepSet s ∧ ∀ v ∉ s, ∃ w ∈ s, G.Adj v w)
    isMaximalIndepSet_iff_forall_exists_adj.symm

/-- The maximal independent sets of a finite graph. -/
def maximalIndepSets : Finset (Finset V) := {s | Maximal G.IsIndepSet (s : Set V)}

@[simp] theorem mem_maximalIndepSets : s ∈ G.maximalIndepSets ↔ Maximal G.IsIndepSet ↑s :=
  Finset.mem_filter_univ _

/-- No maximal independent set contains another. -/
theorem isAntichain_maximalIndepSets :
    IsAntichain (· ⊆ ·) (G.maximalIndepSets : Set (Finset V)) := fun _ hs _ ht hne hst ↦
  hne <| Finset.coe_injective <| (G.mem_maximalIndepSets.1 hs).eq_of_subset
    (G.mem_maximalIndepSets.1 ht).prop (Finset.coe_subset.2 hst)

end SimpleGraph
