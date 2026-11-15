/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Vertex sets that induce a connected graph

`[UPSTREAM]` candidates for `Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean` and
`Mathlib/Combinatorics/SimpleGraph/Hasse.lean`. The sets `s` with `(G.induce s).Connected`
determine `G`, as [two distinct vertices induce a connected graph exactly when they are
adjacent](##SimpleGraph.induce_pair_connected_iff). Under the complete graph they are all the
nonempty sets, and under the Hasse diagram of a linear order [the nonempty
intervals](##SimpleGraph.induce_hasse_connected_iff). A finite set is shown to be one by
[adding its vertices one at a time](##SimpleGraph.induce_coe_insert_connected), each adjacent to
one already there.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s : Set V}

/-- A preconnected graph has an edge from any set that is neither empty nor everything to its
complement. -/
theorem Preconnected.exists_adj_of_mem_of_notMem (hG : G.Preconnected) {t : Set V} {u w : V}
    (hu : u ∈ t) (hw : w ∉ t) : ∃ a ∈ t, ∃ b ∉ t, G.Adj a b := by
  obtain ⟨p⟩ := hG u w
  obtain ⟨d, -, hd, hd'⟩ := p.exists_boundary_dart t hu hw
  exact ⟨d.fst, hd, d.snd, hd', d.adj⟩

/-- A set that induces a preconnected graph and meets both `t` and its complement has an edge
from `t` to the complement. -/
theorem exists_adj_of_induce_preconnected (hs : (G.induce s).Preconnected) {t : Set V} {u w : V}
    (hu : u ∈ s) (hut : u ∈ t) (hw : w ∈ s) (hwt : w ∉ t) :
    ∃ a ∈ s, ∃ b ∈ s, a ∈ t ∧ b ∉ t ∧ G.Adj a b := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    hs.exists_adj_of_mem_of_notMem (t := Subtype.val ⁻¹' t) (u := ⟨u, hu⟩) (w := ⟨w, hw⟩) hut hwt
  exact ⟨a, a.2, b, b.2, ha, hb, hab⟩

theorem induce_singleton_connected (v : V) : (G.induce {v}).Connected :=
  have : Nonempty ({v} : Set V) := ⟨⟨v, rfl⟩⟩
  .of_subsingleton

/-- Adding a vertex adjacent to a vertex of the set keeps the induced graph connected. -/
theorem Connected.induce_insert (hs : (G.induce s).Connected) {u v : V} (hu : u ∈ s)
    (h : G.Adj v u) : (G.induce (insert v s)).Connected := by
  rw [← Set.union_singleton]
  exact connected_induce_union hs.preconnected (induce_singleton_connected v).preconnected hu rfl
    h.symm

/-- Two distinct vertices induce a connected graph exactly when they are adjacent. -/
theorem induce_pair_connected_iff {u v : V} (h : u ≠ v) :
    (G.induce {u, v}).Connected ↔ G.Adj u v := by
  refine ⟨fun hc ↦ ?_, induce_pair_connected_of_adj⟩
  obtain ⟨a, -, b, hb, rfl, hba, hab⟩ := exists_adj_of_induce_preconnected hc.preconnected
    (t := {u}) (Set.mem_insert _ _) rfl (by simp) h.symm
  exact hb.resolve_left hba ▸ hab

/-- Under the complete graph every nonempty set induces a connected graph. -/
theorem induce_top_connected_iff : ((⊤ : SimpleGraph V).induce s).Connected ↔ s.Nonempty := by
  rw [induce_top, connected_top_iff, Set.nonempty_coe_sort]

/-! ### Finite sets -/

theorem induce_coe_singleton_connected (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)).Connected := by
  rw [Finset.coe_singleton]
  exact induce_singleton_connected v

/-- Adding to a finite set a vertex adjacent to one of its vertices keeps the induced graph
connected. -/
theorem induce_coe_insert_connected [DecidableEq V] {s : Finset V} {v : V}
    (hs : (G.induce (↑s : Set V)).Connected) (h : ∃ u ∈ s, G.Adj v u) :
    (G.induce (↑(insert v s) : Set V)).Connected := by
  obtain ⟨u, hu, h⟩ := h
  rw [Finset.coe_insert]
  exact hs.induce_insert (Finset.mem_coe.2 hu) h

/-! ### Hasse diagrams -/

section Hasse

variable {α : Type*} {s : Set α}

/-- On an order-connected set the Hasse diagram of the order induces the Hasse diagram of the
set. -/
theorem induce_hasse_of_ordConnected [Preorder α] (hs : s.OrdConnected) :
    (hasse α).induce s = hasse s := by
  ext a b
  have key (a b : s) : (a : α) ⋖ b ↔ a ⋖ b :=
    Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype (· ∈ s)) (by simpa using hs)
  simp [hasse_adj, key]

variable [LinearOrder α]

/-- Under the Hasse diagram of a linear order in which every element is reached by successors,
the sets that induce a preconnected graph are the intervals. -/
theorem induce_hasse_preconnected_iff [SuccOrder α] [IsSuccArchimedean α] :
    ((hasse α).induce s).Preconnected ↔ s.OrdConnected := by
  refine ⟨fun hc ↦ ⟨fun a ha b hb x hx ↦ ?_⟩, fun hs ↦ ?_⟩
  · obtain ⟨p⟩ := hc ⟨a, ha⟩ ⟨b, hb⟩
    have hmem := (p.map (Embedding.induce s).toHom).mem_support_hasse_of_ge_of_le _ hx.1 hx.2
    rw [Walk.support_map] at hmem
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hmem
    exact y.2
  · rw [induce_hasse_of_ordConnected hs]
    exact preconnected_hasse_of_succOrder s

/-- Under the Hasse diagram of a locally finite linear order, the sets that induce a connected
graph are the nonempty intervals. -/
theorem induce_hasse_connected_iff [LocallyFiniteOrder α] :
    ((hasse α).induce s).Connected ↔ s.Nonempty ∧ s.OrdConnected := by
  let := LinearLocallyFiniteOrder.succOrder α
  rw [connected_iff, induce_hasse_preconnected_iff, Set.nonempty_coe_sort, and_comm]

end Hasse

end SimpleGraph
