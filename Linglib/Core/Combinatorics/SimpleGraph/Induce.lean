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
adjacent](##SimpleGraph.induce_pair_connected_iff), and there are more of them the more edges `G`
has: every nonempty set under the complete graph, and under the Hasse diagram of a locally finite
linear order [the nonempty intervals](##SimpleGraph.induce_hasse_connected_iff), of which those
containing a least element are [the nonempty lower
sets](##SimpleGraph.induce_hasse_connected_and_bot_mem_iff).
-/

public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {s : Set V}

/-- A set that induces a connected graph still does so when edges are added. -/
theorem induce_connected_mono (h : G ≤ H) (hs : (G.induce s).Connected) :
    (H.induce s).Connected :=
  hs.mono (comap_monotone _ h)

theorem induce_singleton_connected (v : V) : (G.induce {v}).Connected :=
  have : Nonempty ({v} : Set V) := ⟨⟨v, rfl⟩⟩
  .of_subsingleton

/-- Adding a vertex adjacent to a vertex of the set keeps the induced graph connected. -/
theorem Connected.induce_insert (hs : (G.induce s).Connected) {u v : V} (hu : u ∈ s)
    (h : G.Adj v u) : (G.induce (insert v s)).Connected := by
  rw [← Set.union_singleton]
  exact connected_induce_union hs.preconnected (induce_singleton_connected v).preconnected hu rfl
    h.symm

/-- A set that induces a connected graph and meets both `t` and its complement has an edge from
`t` to the complement. -/
theorem exists_adj_of_induce_connected (hs : (G.induce s).Connected) {t : Set V} {u w : V}
    (hu : u ∈ s) (hut : u ∈ t) (hw : w ∈ s) (hwt : w ∉ t) :
    ∃ a ∈ s, ∃ b ∈ s, a ∈ t ∧ b ∉ t ∧ G.Adj a b := by
  obtain ⟨p⟩ := hs.preconnected ⟨u, hu⟩ ⟨w, hw⟩
  obtain ⟨d, -, hd, hd'⟩ := p.exists_boundary_dart (Subtype.val ⁻¹' t) hut hwt
  exact ⟨d.fst, d.fst.2, d.snd, d.snd.2, hd, hd', d.adj⟩

/-- Two distinct vertices induce a connected graph exactly when they are adjacent. -/
theorem induce_pair_connected_iff {u v : V} (h : u ≠ v) :
    (G.induce {u, v}).Connected ↔ G.Adj u v := by
  refine ⟨fun hc ↦ by_contra fun hadj ↦ ?_, induce_pair_connected_of_adj⟩
  have hadj' : ¬ G.Adj v u := fun h ↦ hadj h.symm
  have hbot : G.induce {u, v} = ⊥ := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;> simp [hadj, hadj']
  have hr := hc.preconnected ⟨u, by simp⟩ ⟨v, by simp⟩
  rw [hbot, reachable_bot] at hr
  exact h (congrArg Subtype.val hr)

/-- Under the complete graph every nonempty set induces a connected graph. -/
theorem induce_top_connected_iff : ((⊤ : SimpleGraph V).induce s).Connected ↔ s.Nonempty := by
  rw [induce_top]
  refine ⟨fun hc ↦ Set.nonempty_coe_sort.1 hc.nonempty, fun hs ↦ ?_⟩
  have := Set.nonempty_coe_sort.2 hs
  exact connected_top

/-- Under the Hasse diagram of a locally finite linear order, the sets that induce a connected
graph are the nonempty intervals. -/
theorem induce_hasse_connected_iff {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    {s : Set α} : ((hasse α).induce s).Connected ↔ s.Nonempty ∧ s.OrdConnected := by
  classical
  refine ⟨fun hc ↦ ⟨Set.nonempty_coe_sort.1 hc.nonempty, ⟨fun a ha b hb x hx ↦ ?_⟩⟩,
    fun ⟨hne, hs⟩ ↦ ?_⟩
  · obtain ⟨p⟩ := hc.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    have hmem := (p.map (Embedding.induce s).toHom).mem_support_hasse_of_ge_of_le _ hx.1 hx.2
    rw [Walk.support_map] at hmem
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hmem
    exact y.2
  · have := Set.nonempty_coe_sort.2 hne
    let := LinearLocallyFiniteOrder.succOrder s
    have hle : hasse s ≤ (hasse α).induce s := fun a b hab ↦ by
      have hcov {a b : s} (h : a ⋖ b) : (a : α) ⋖ b :=
        ⟨h.lt, fun c hac hcb ↦ h.2 (c := ⟨c, hs.out a.2 b.2 ⟨hac.le, hcb.le⟩⟩) hac hcb⟩
      exact hasse_adj.2 ((hasse_adj.1 hab).imp hcov hcov)
    exact ⟨(preconnected_hasse_of_succOrder s).mono hle⟩

/-- Under the Hasse diagram of a locally finite linear order with a least element, the sets that
induce a connected graph and contain the least element are the nonempty lower sets. -/
theorem induce_hasse_connected_and_bot_mem_iff {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] {s : Set α} :
    ((hasse α).induce s).Connected ∧ ⊥ ∈ s ↔ s.Nonempty ∧ IsLowerSet s := by
  rw [induce_hasse_connected_iff]
  exact ⟨fun ⟨⟨hne, hc⟩, hb⟩ ↦ ⟨hne, fun _ _ hba ha ↦ hc.out hb ha ⟨bot_le, hba⟩⟩,
    fun ⟨hne, hl⟩ ↦ ⟨⟨hne, hl.ordConnected⟩, hl bot_le hne.some_mem⟩⟩

end SimpleGraph
