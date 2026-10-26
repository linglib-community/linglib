/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.ContractUnary
public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Linglib.Core.Data.UnorderedTree.Licensed
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Vertex conservation for pruning cuts

A pruning cut removes its crown subtrees entirely, so crown vertices and trunk vertices recover
the vertices of the tree exactly. Hence every crown component, and the trunk of a proper cut, is
smaller than the tree: the descent that makes recursions over cuts, such as the antipode, well
founded. Contracting the vertices the cut leaves with a single child then removes one more
vertex for each.

## Main results

* `ConnesKreimer.cutSummandsN_numNodes`, `hasExtractionCost_numNodes_cutSummandsN`: vertex
  conservation for the nonplanar pruning cuts, and for a choice of them over a forest.
* `ConnesKreimer.cutSummandsN_crown_numNodes_lt`, `ConnesKreimer.cutSummandsN_trunk_numNodes_lt`:
  crowns and proper trunks are smaller than the tree.
* `ConnesKreimer.cutSummandsN_numEdges_contractUnary`: the edges of the tree, of the crown and of
  the contracted trunk.
* `ConnesKreimer.cutSummandsN_numUnary`: in a full binary tree a cut leaves a unary vertex for each
  tree it extracts, less two for each vertex both of whose children it extracts.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α : Type*}

/-! ### Vertex conservation for the pruning cuts -/

/-- The crown and the trunk of a pruning cut have exactly the vertices of the tree. -/
theorem cutSummandsN_numNodes (T : UnorderedTree α) :
    ∀ p ∈ cutSummandsN T,
      (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes = T.numNodes :=
  Quotient.inductionOn T fun t p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projSummand, Multiset.map_map, Function.comp_def] using
      cutSummandsG_numNodes pruning (k := 0) (fun _ _ h ↦ by cases h; rfl) t q hq

/-- A choice of pruning cuts conserves vertices. -/
theorem hasExtractionCost_numNodes_cutSummandsN {F : Multiset (UnorderedTree α)} {s : CutChoice α}
    (hs : s ∈ forestCutChoicesG cutSummandsN F) :
    s.HasExtractionCost UnorderedTree.numNodes 0 :=
  .of_mem_forestCutChoicesG hs fun x _ p hp _ ↦ by simpa using (cutSummandsN_numNodes x.1 p hp).symm

theorem cutSummandsN_crown_ne_singleton (T : UnorderedTree α)
    (p : Multiset (UnorderedTree α) × UnorderedTree α) (hp : p ∈ cutSummandsN T) :
    p.1 ≠ ({T} : Multiset (UnorderedTree α)) := by
  intro hcrown
  have hw := cutSummandsN_numNodes T p hp
  rw [hcrown] at hw
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hw
  have := p.2.numNodes_pos
  omega

/-- Every crown component of a pruning cut has fewer vertices than the tree. -/
theorem cutSummandsN_crown_numNodes_lt {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T)
    {t : UnorderedTree α} (ht : t ∈ p.1) : t.numNodes < T.numNodes := by
  have hw := cutSummandsN_numNodes T p hp
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem UnorderedTree.numNodes ht)
  have := p.2.numNodes_pos
  omega

/-- The trunk of a pruning cut with a nonempty crown has fewer vertices than the tree. -/
theorem cutSummandsN_trunk_numNodes_lt {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T)
    (h : p.1 ≠ 0) : p.2.numNodes < T.numNodes := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero h
  have hw := cutSummandsN_numNodes T p hp
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem UnorderedTree.numNodes ht)
  have := t.numNodes_pos
  omega

theorem cutSummandsN_crown_numEdges_lt {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T)
    (h : p.1 ≠ 0) : (p.1.map UnorderedTree.numEdges).sum < T.numEdges := by
  have hw := cutSummandsN_numNodes T p hp
  rw [UnorderedTree.sum_map_numNodes] at hw
  have := Multiset.card_pos.mpr h
  have := p.2.numNodes_pos
  have := T.numEdges_add_one
  omega

theorem cutSummandsN_self_not_mem_crown (T : UnorderedTree α)
    (p : Multiset (UnorderedTree α) × UnorderedTree α) (hp : p ∈ cutSummandsN T) :
    T ∉ p.1 :=
  fun h ↦ (cutSummandsN_crown_numNodes_lt hp h).false

/-! ### Unary vertices left by a pruning cut

In a full binary tree a pruning cut leaves the parent of each tree it extracts with a single child,
unless it extracts both of the parent's children, which leaves the parent a leaf. Contracting the
unary vertices of the trunk then removes one more vertex for each. -/

/-- Deleting the crown of a pruning cut and contracting the unary vertices of its trunk removes,
    besides the crown's own edges, one edge for each crown component and one for each unary
    vertex. -/
theorem cutSummandsN_numEdges_contractUnary {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T) :
    T.numEdges = (p.1.map UnorderedTree.numEdges).sum + p.2.contractUnary.numEdges +
      Multiset.card p.1 + p.2.numUnary := by
  have hw := cutSummandsN_numNodes T p hp
  rw [UnorderedTree.sum_map_numNodes] at hw
  have := UnorderedTree.numNodes_contractUnary_add_numUnary p.2
  have := T.numEdges_add_one
  have := p.2.contractUnary.numEdges_add_one
  omega

private theorem cutSummandsG_pruning_numUnary (t : RoseTree α)
    (ht : t.Licensed fun _ ks ↦ Multiset.card (ks : Multiset α) = 0 ∨
      Multiset.card (ks : Multiset α) = 2) :
    ∀ p ∈ cutSummandsG pruning t, ∃ k, Multiset.card p.1 = p.2.numUnary + 2 * k := fun p hp ↦ by
  obtain ⟨-, k, hk⟩ := cutSummandsG_induction pruning
    (P := fun cs q ↦ (∀ c ∈ cs, c.Licensed fun _ ks ↦ Multiset.card (ks : Multiset α) = 0 ∨
        Multiset.card (ks : Multiset α) = 2) →
      q.2.length ≤ cs.length ∧
        ∃ k, Multiset.card q.1 + q.2.length = cs.length + (q.2.map RoseTree.numUnary).sum + 2 * k)
    (fun _ ↦ ⟨le_rfl, 0, rfl⟩)
    (fun _ _ h _ ↦ by cases h; exact ⟨by simp, 0, by simp⟩)
    (fun a cs ⟨crown, rest⟩ _ hP hL ↦ by
      have ht := hL _ (List.mem_singleton_self _)
      obtain ⟨hlen, k, hk⟩ := hP fun _ hc ↦ ht.of_mem hc
      have hcs : cs.length = 0 ∨ cs.length = 2 := by simpa using ht.rel_root
      refine ⟨by simp, ?_⟩
      rcases rest with _ | ⟨d, _ | ⟨e, rest⟩⟩
      · simp only [List.length_nil, List.map_nil, List.sum_nil, add_zero] at hk
        rcases hcs with h | h
        · exact ⟨k, by simp; omega⟩
        · exact ⟨k + 1, by simp; omega⟩
      · simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil] at hk hlen
        exact ⟨k, by simp; omega⟩
      · simp only [List.length_cons, List.map_cons, List.sum_cons] at hk hlen
        exact ⟨k, by simp; omega⟩)
    (fun _ _ _ _ _ _ ha hb hL ↦ by
      obtain ⟨h₁, k₁, hk₁⟩ := ha fun c hc ↦
        hL c (List.mem_cons.mpr (.inl (List.mem_singleton.mp hc)))
      obtain ⟨h₂, k₂, hk₂⟩ := hb fun c hc ↦ hL c (List.mem_cons_of_mem _ hc)
      refine ⟨?_, k₁ + k₂, ?_⟩ <;>
      · simp only [Multiset.card_add, List.length_append, List.map_append, List.sum_append,
          List.length_cons, List.length_nil] at *
        omega)
    t p hp (by simpa using ht)
  exact ⟨k, by simp at hk; omega⟩

/-- In a full binary tree a pruning cut leaves a unary vertex for each tree it extracts, less two
    for each vertex both of whose children it extracts. -/
theorem cutSummandsN_numUnary {T : UnorderedTree α} (hT : T.IsFullBinary)
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T) :
    ∃ k, Multiset.card p.1 = p.2.numUnary + 2 * k := by
  induction T using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projSummand] using cutSummandsG_pruning_numUnary t hT q hq

end ConnesKreimer
