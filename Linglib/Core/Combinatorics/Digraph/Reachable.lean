/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Maps
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Data.Fintype.Basic

/-!
# Reachability in a digraph

A vertex `w` is reachable from `v` when a possibly empty chain of arcs leads from `v` to `w`. This
file defines reachability and the set of vertices reachable from a vertex.

## Main definitions

* `Digraph.Reachable`: the reflexive transitive closure of adjacency.
* `Digraph.reachSet`: the vertices reachable from a vertex, the vertex included.

## Implementation notes

`Digraph.Reachable` is an `abbrev` for `Relation.ReflTransGen G.Adj`, so mathlib's closure API
applies to it and it is decidable on a finite vertex type by `Core/Relation/ReflTransGen.lean`.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V W : Type*} {G : Digraph V} {u v w x y : V}

instance {α : Type*} {r : α → α → Prop} [DecidableRel r] : DecidableRel (SymmGen r) :=
  fun a b ↦ inferInstanceAs (Decidable (r a b ∨ r b a))

/-- `w` is reachable from `v` when a possibly empty chain of arcs leads from `v` to `w`. -/
abbrev Reachable (G : Digraph V) : V → V → Prop := ReflTransGen G.Adj

/-- The vertices reachable from `v`, `v` itself included. -/
def reachSet (G : Digraph V) (v : V) : Set V := {x | G.Reachable v x}

@[simp] theorem mem_reachSet : x ∈ G.reachSet v ↔ G.Reachable v x := Iff.rfl

instance [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.reachSet v) :=
  fun _ ↦ inferInstanceAs (Decidable (G.Reachable v _))

theorem exists_adj_mem_reachSet (hx : x ∈ G.reachSet v) (hne : x ≠ v) :
    ∃ u, G.Adj v u ∧ x ∈ G.reachSet u :=
  (ReflTransGen.cases_head hx).resolve_left hne.symm

/-- Two vertices reachable from `v`, one inside a set and one outside, are separated by an arc
between vertices reachable from `v`. -/
theorem exists_symmGen_adj_of_mem_of_notMem {S : Set V} (hx : G.Reachable v x)
    (hy : G.Reachable v y) (hxS : x ∈ S) (hyS : y ∉ S) :
    ∃ p q, SymmGen G.Adj p q ∧ G.Reachable v p ∧ G.Reachable v q ∧ p ∈ S ∧ q ∉ S := by
  by_cases hv : v ∈ S
  · obtain ⟨p, q, hpq, hpS, hqS, hvp, -⟩ := hy.exists_boundary hv hyS
    exact ⟨p, q, .inl hpq, hvp, hvp.tail hpq, hpS, hqS⟩
  · obtain ⟨p, q, hpq, hpS, hqS, hvp, -⟩ := hx.exists_boundary (S := Sᶜ) hv (not_not_intro hxS)
    exact ⟨q, p, .inr hpq, hvp.tail hpq, hvp, not_not.1 hqS, hpS⟩

/-- Vertices reachable from a common vertex, neither reachable from the other, lie under distinct
out-neighbours of one vertex. -/
theorem exists_adj_adj_of_not_reachable (hu : G.Reachable x u) (hv : G.Reachable x v)
    (huv : ¬ G.Reachable u v) (hvu : ¬ G.Reachable v u) :
    ∃ p u' v', G.Adj p u' ∧ G.Adj p v' ∧ u' ≠ v' ∧ G.Reachable u' u ∧ G.Reachable v' v := by
  obtain ⟨p, u', hpu', hp, hu', -, hu'u⟩ :=
    hu.exists_boundary (S := {z | G.Reachable z v}) hv huv
  obtain rfl | ⟨v', hpv', hv'v⟩ := ReflTransGen.cases_head hp
  · exact absurd (hu'u.head hpu') hvu
  · exact ⟨p, u', v', hpu', hpv', fun h ↦ hu' (h ▸ hv'v), hu'u, hv'v⟩

/-- An equivalence of vertices preserves and reflects reachability. -/
theorem reachable_comap (e : W ≃ V) {a b : W} :
    (G.comap e).Reachable a b ↔ G.Reachable (e a) (e b) :=
  ⟨fun h ↦ ReflTransGen.lift (r := (G.comap e).Adj) (p := G.Adj) e (fun _ _ h ↦ h) _ _ h,
    fun h ↦ by
      simpa [Function.onFun] using ReflTransGen.lift (r := G.Adj) (p := (G.comap e).Adj) e.symm
        (fun a b h ↦ by simpa using h) _ _ h⟩

theorem reachSet_comap (e : W ≃ V) (a : W) : (G.comap e).reachSet a = e ⁻¹' G.reachSet (e a) :=
  Set.ext fun _ ↦ reachable_comap e

end Digraph
