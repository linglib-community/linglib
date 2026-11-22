/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.RelIso.Basic

/-!
# Transport of dependency graphs

A permutation of the positions of a sentence carries a dependency graph to the graph of the same
words and arcs in another order. Properties of the structure alone, such as dominance, treehood
and valency, are invariant under transport; properties of the linearization, such as projectivity
and dependency length, are not, and the files that define them say how they vary.

## Main definitions

* `Graph.map`: a graph transported along a permutation of its positions. Transport is an action
  of the permutations on the graphs, written `σ • g`, and `Graph.mapRelIso` is the isomorphism it
  gives between the arcs of a graph and those of its transport.
* `Graph.mirror`: the graph read in reverse.
* `Graph.linearize`: the graph read in a given order of its positions.
-/

@[expose] public section

namespace DependencyGrammar

variable {L : Type*} {n : ℕ}

/-- `g.map σ` transports `g` along the position permutation `σ`. Arcs and root move
together, so the labeled structure is unchanged and only the linearization varies. -/
def Graph.map (g : Graph L n) (σ : Equiv.Perm (Fin n)) : Graph L n :=
  { label := fun v w ↦ g.label (σ.symm v) (σ.symm w)
    root := σ g.root }

@[simp] theorem Graph.map_adj (g : Graph L n) (σ : Equiv.Perm (Fin n))
    (v w : Fin n) : (g.map σ).Adj v w ↔ g.Adj (σ.symm v) (σ.symm w) :=
  Iff.rfl

@[simp] theorem Graph.map_linked (g : Graph L n) (σ : Equiv.Perm (Fin n))
    (v w : Fin n) : (g.map σ).Linked v w ↔ g.Linked (σ.symm v) (σ.symm w) :=
  Iff.rfl

@[simp] theorem Graph.map_one (g : Graph L n) : g.map 1 = g := rfl

theorem Graph.map_map (g : Graph L n) (σ τ : Equiv.Perm (Fin n)) :
    (g.map σ).map τ = g.map (τ * σ) := rfl

/-- The permutations of the positions act on the dependency graphs by transport. The orbit of a
graph is the set of its linearizations. -/
instance : MulAction (Equiv.Perm (Fin n)) (Graph L n) where
  smul σ g := g.map σ
  one_smul := Graph.map_one
  mul_smul σ τ g := (g.map_map τ σ).symm

theorem Graph.smul_def (σ : Equiv.Perm (Fin n)) (g : Graph L n) : σ • g = g.map σ := rfl

/-- A permutation of the positions is an isomorphism from the arcs of a graph to the arcs of its
transport. -/
def Graph.mapRelIso (g : Graph L n) (σ : Equiv.Perm (Fin n)) : g.Adj ≃r (g.map σ).Adj :=
  ⟨σ, by simp⟩

@[simp] theorem Graph.coe_mapRelIso (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    ⇑(g.mapRelIso σ) = σ := rfl

theorem Graph.map_adj_apply (g : Graph L n) (σ : Equiv.Perm (Fin n)) (v w : Fin n) :
    (g.map σ).Adj (σ v) (σ w) ↔ g.Adj v w :=
  (g.mapRelIso σ).map_rel_iff

/-- The undirected view of a transported graph is the undirected view pulled back along the
inverse permutation. -/
theorem Graph.toSimpleGraph_map (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    (g.map σ).toSimpleGraph = g.toSimpleGraph.comap σ.symm := by
  ext v w
  simp

/-- The mirror image, transported along position reversal. -/
def Graph.mirror (g : Graph L n) : Graph L n := g.map Fin.revPerm

@[simp] theorem Graph.mirror_adj (g : Graph L n) (v w : Fin n) :
    g.mirror.Adj v w ↔ g.Adj v.rev w.rev :=
  Iff.rfl

@[simp] theorem Graph.mirror_mirror (g : Graph L n) : g.mirror.mirror = g := by
  ext <;> simp [Graph.mirror, Graph.map]

theorem Graph.mirror_involutive : Function.Involutive (Graph.mirror (L := L) (n := n)) :=
  Graph.mirror_mirror

/-- The graph read in the order `order`, which lists every position once. The token at
position `p` is the token of `g` at `order[p]`, arcs and root following. -/
def Graph.linearize (g : Graph L n) (order : List (Fin n)) (h : order.Perm (List.finRange n)) :
    Graph L n :=
  g.map ((finCongr (h.length_eq.trans List.length_finRange).symm).trans
    ((h.nodup_iff.mpr (List.nodup_finRange n)).getEquivOfForallMemList order
      fun x ↦ h.mem_iff.mpr (List.mem_finRange x))).symm

end DependencyGrammar
