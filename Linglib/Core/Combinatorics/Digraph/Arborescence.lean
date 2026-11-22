/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Finite
public import Linglib.Core.Combinatorics.Digraph.Reachable
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Branchings and arborescences

A digraph is a branching when no vertex is reachable from one of its out-neighbours and no vertex
has two in-neighbours, and an arborescence with root `r` when in addition every vertex is
reachable from `r`. In a branching, reachability is a partial order in which the vertices reaching
a given vertex form a chain, so two vertices neither of which reaches the other have disjoint
reach sets.

## Main definitions

* `Digraph.IsBranching`: no directed cycle, and at most one in-neighbour for each vertex.
* `Digraph.IsArborescence`: a branching all of whose vertices are reachable from a root.

## Main statements

* `Digraph.isArborescence_iff_forall_not_adj_iff`: an arborescence is a branching whose only vertex
  without an in-neighbour is the root.
* `Digraph.isArborescence_iff_leftUnique_adj`: acyclicity follows when no vertex has two
  in-neighbours, the root has none, and every vertex is reachable from the root.
* `Digraph.IsBranching.disjoint_reachSet`: vertices neither of which reaches the other have
  disjoint reach sets.
* `Digraph.IsArborescence.card_arcs_add_one`: an arborescence has one arc fewer than vertices.

## Implementation notes

The root is an argument of `IsArborescence` and not data of the digraph; it is determined by the
digraph (`Digraph.IsArborescence.root_unique`). Mathlib's `Quiver.Arborescence` is the same notion
for a quiver, a class on the vertex type; here several digraphs on one vertex type are compared, so
the notion is a predicate on a digraph.

## TODO

* The reachability order of a branching as a `PredOrder`, with the in-neighbour as predecessor.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V W : Type*} {G : Digraph V} {r u v w x : V}

/-- A digraph is a branching when no vertex is reachable from one of its out-neighbours and no
vertex has two in-neighbours. -/
structure IsBranching (G : Digraph V) : Prop where
  /-- There is no directed cycle: a vertex is not reachable from its out-neighbours. -/
  not_reachable_of_adj ⦃v w : V⦄ : G.Adj v w → ¬ G.Reachable w v
  /-- A vertex has at most one in-neighbour. -/
  leftUnique_adj : Relator.LeftUnique G.Adj

/-- A digraph is an arborescence with root `r` when it is a branching in which every vertex is
reachable from `r`. -/
structure IsArborescence (G : Digraph V) (r : V) : Prop extends G.IsBranching where
  /-- Every vertex is reachable from the root. -/
  reachable (v : V) : G.Reachable r v

namespace IsBranching

variable (hB : G.IsBranching)
include hB

theorem not_adj_self : ¬ G.Adj v v := fun h ↦ hB.not_reachable_of_adj h .refl

theorem ne_of_adj (h : G.Adj v w) : v ≠ w := by
  rintro rfl
  exact hB.not_adj_self h

theorem not_transGen_self (v : V) : ¬ TransGen G.Adj v v := fun h ↦
  have ⟨_, hvw, hwv⟩ := TransGen.head'_iff.1 h
  hB.not_reachable_of_adj hvw hwv

/-- In a finite branching the in-neighbours are reached in finitely many steps. -/
theorem wellFounded_transGen [Finite V] : WellFounded (TransGen G.Adj) :=
  haveI : Std.Irrefl (TransGen G.Adj) := ⟨hB.not_transGen_self⟩
  Finite.wellFounded_of_trans_of_irrefl _

theorem reachable_antisymm (hvw : G.Reachable v w) (hwv : G.Reachable w v) : v = w := by
  obtain rfl | ⟨u, hvu, huw⟩ := ReflTransGen.cases_head hvw
  · rfl
  · exact absurd (huw.trans hwv) (hB.not_reachable_of_adj hvu)

/-- A vertex that reaches another, different one reaches its in-neighbour. -/
theorem reachable_of_reachable_of_adj (hvw : G.Reachable v w) (hne : v ≠ w) (hu : G.Adj u w) :
    G.Reachable v u := by
  obtain rfl | ⟨z, hvz, hzw⟩ := ReflTransGen.cases_tail hvw
  · exact absurd rfl hne
  · exact hB.leftUnique_adj hzw hu ▸ hvz

theorem reachable_total (hv : G.Reachable v x) (hw : G.Reachable w x) :
    G.Reachable v w ∨ G.Reachable w v :=
  ReflTransGen.total_of_left_unique hB.leftUnique_adj hv hw

/-- Vertices of a branching neither of which reaches the other have disjoint reach sets. -/
theorem disjoint_reachSet (hvw : ¬ G.Reachable v w) (hwv : ¬ G.Reachable w v) :
    Disjoint (G.reachSet v) (G.reachSet w) :=
  Set.disjoint_left.2 fun _ hv hw ↦ (hB.reachable_total hv hw).elim hvw hwv

theorem disjoint_reachSet_of_adj (hw : G.Adj v w) (hu : G.Adj v u) (hne : w ≠ u) :
    Disjoint (G.reachSet w) (G.reachSet u) :=
  hB.disjoint_reachSet
    (fun hd ↦ hB.not_reachable_of_adj hw (hB.reachable_of_reachable_of_adj hd hne hu))
    fun hd ↦ hB.not_reachable_of_adj hu (hB.reachable_of_reachable_of_adj hd hne.symm hw)

theorem reachSet_injective : Function.Injective G.reachSet := fun v w h ↦
  hB.reachable_antisymm (h ▸ (ReflTransGen.refl : G.Reachable w w) : w ∈ G.reachSet v)
    (h.symm ▸ (ReflTransGen.refl : G.Reachable v v) : v ∈ G.reachSet w)

/-- A branching pulled back along an equivalence is a branching. -/
theorem comap (e : W ≃ V) : (G.comap e).IsBranching where
  not_reachable_of_adj _ _ h hd := hB.not_reachable_of_adj h ((reachable_comap e).1 hd)
  leftUnique_adj _ _ _ hu hv := e.injective (hB.leftUnique_adj hu hv)

end IsBranching

namespace IsArborescence

variable (hA : G.IsArborescence r)
include hA

theorem not_adj_root (v : V) : ¬ G.Adj v r := fun h ↦
  hA.not_reachable_of_adj h (hA.reachable v)

theorem exists_adj_of_ne_root (hw : w ≠ r) : ∃ v, G.Adj v w :=
  ((ReflTransGen.cases_tail (hA.reachable w)).resolve_left hw).imp fun _ h ↦ h.2

/-- An arborescence has one root. -/
theorem root_unique {r' : V} (hA' : G.IsArborescence r') : r = r' :=
  hA.reachable_antisymm (hA.reachable r') (hA'.reachable r)

/-- An arborescence pulled back along an equivalence is an arborescence. -/
theorem comap (e : W ≃ V) : (G.comap e).IsArborescence (e.symm r) where
  toIsBranching := hA.toIsBranching.comap e
  reachable v := (reachable_comap e).2 (by simpa using hA.reachable (e v))

/-- An arborescence has one arc fewer than vertices: each vertex but the root is the head of the
one arc from its in-neighbour. -/
theorem card_arcs_add_one [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.arcs.card + 1 = Fintype.card V := by
  rw [← Finset.card_univ, ← Finset.card_erase_add_one (Finset.mem_univ r)]
  refine congrArg (· + 1) (Finset.card_bij (fun a _ ↦ a.2) ?_ ?_ ?_)
  · rintro ⟨v, w⟩ h
    exact Finset.mem_erase.2
      ⟨fun e ↦ hA.not_adj_root v (e ▸ (mem_arcs (p := (v, w))).1 h), Finset.mem_univ _⟩
  · rintro ⟨v, w⟩ h ⟨v', w'⟩ h' (rfl : w = w')
    have e : v = v' := hA.leftUnique_adj ((mem_arcs (p := (v, w))).1 h)
      ((mem_arcs (p := (v', w))).1 h')
    rw [e]
  · intro w hw
    obtain ⟨v, hv⟩ := hA.exists_adj_of_ne_root (Finset.ne_of_mem_erase hw)
    exact ⟨(v, w), (mem_arcs (p := (v, w))).2 hv, rfl⟩

end IsArborescence

/-- An arborescence is a branching whose only vertex without an in-neighbour is the root. -/
theorem isArborescence_iff_forall_not_adj_iff [Finite V] :
    G.IsArborescence r ↔ G.IsBranching ∧ ∀ w, (∀ v, ¬ G.Adj v w) ↔ w = r := by
  refine ⟨fun hA ↦ ⟨hA.toIsBranching, fun w ↦ ⟨fun hw ↦ ?_, fun hw ↦ hw ▸ hA.not_adj_root⟩⟩,
    fun ⟨hB, h⟩ ↦ ⟨hB, ReflTransGen.of_forall_exists hB.not_transGen_self fun w hw ↦ ?_⟩⟩
  · by_contra hne
    exact (hA.exists_adj_of_ne_root hne).elim hw
  · by_contra hno
    exact hw ((h w).1 fun v hv ↦ hno ⟨v, hv⟩)

/-- A digraph is an arborescence when no vertex has two in-neighbours, the root has none, and every
vertex is reachable from the root. -/
theorem isArborescence_iff_leftUnique_adj :
    G.IsArborescence r ↔
      Relator.LeftUnique G.Adj ∧ (∀ v, ¬ G.Adj v r) ∧ ∀ v, G.Reachable r v := by
  refine ⟨fun hA ↦ ⟨hA.leftUnique_adj, hA.not_adj_root, hA.reachable⟩,
    fun ⟨hU, hr, hd⟩ ↦ ⟨⟨fun v w hvw hwv ↦ ?_, hU⟩, hd⟩⟩
  have hroot : ¬ TransGen G.Adj r r := fun h ↦
    have ⟨y, _, hy⟩ := TransGen.tail'_iff.1 h
    hr y hy
  obtain ⟨c, d, hcd, hc, hdS, -, -⟩ :=
    (hd v).exists_boundary (S := {z | ¬ TransGen G.Adj z z}) hroot
      (not_not_intro (TransGen.head' hvw hwv))
  obtain ⟨y, hdy, hyd⟩ := TransGen.tail'_iff.1 (not_not.1 hdS)
  exact hc (TransGen.head' hcd (hU hyd hcd ▸ hdy))

section Decidable

variable [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]

instance : Decidable G.IsBranching :=
  decidable_of_iff ((∀ v w, G.Adj v w → ¬ G.Reachable w v) ∧
      ∀ w u, G.Adj u w → ∀ v, G.Adj v w → u = v)
    ⟨fun h ↦ ⟨fun _ _ ↦ h.1 _ _, fun _ _ _ hu hv ↦ h.2 _ _ hu _ hv⟩,
      fun h ↦ ⟨fun _ _ ↦ @h.1 _ _, fun _ _ hu _ hv ↦ h.2 hu hv⟩⟩

instance (r : V) : Decidable (G.IsArborescence r) :=
  decidable_of_iff ((∀ w u, G.Adj u w → ∀ v, G.Adj v w → u = v) ∧
      (∀ v, ¬ G.Adj v r) ∧ ∀ v, G.Reachable r v)
    ⟨fun h ↦ isArborescence_iff_leftUnique_adj.2 ⟨fun _ _ _ hu hv ↦ h.1 _ _ hu _ hv, h.2⟩,
      fun h ↦ ⟨fun _ _ hu _ hv ↦ h.leftUnique_adj hu hv, h.not_adj_root, h.reachable⟩⟩

end Decidable

end Digraph
