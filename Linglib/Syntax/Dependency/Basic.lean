/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Maps
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.Fin.Basic

/-!
# Dependency graphs

In dependency grammar the structure of a sentence is a set of *dependencies* between its words.
A dependency links a *head* to one of its *dependents*: in *dogs bark loudly*, the verb *bark* is
the head of *dogs* and of *loudly*.

We represent such a structure as a digraph on the positions of the sentence, with an arc from
each head to each of its dependents. The positions of a sentence of `n` words are `Fin n`, in
the order of the words. A *dependency graph* `Graph L V` is a digraph in which each arc also
carries a relation of type `L`, such as the Universal Dependencies relations `UD.DepRel`.

The terms of dependency grammar are those of digraphs. A word `v` *dominates* a word `w` if `w`
is reachable from `v` (`G.Reachable v w`), and the *yield* of `v` is the set `G.reachSet v` of
the words it dominates. The dependents of `v` are its out-neighbours, and its heads are its
in-neighbours. A *forest* is a branching (`G.IsBranching`), and a *tree* with root `r` is an
arborescence (`G.IsArborescence r`).

This file defines dependency graphs, builds digraphs and dependency graphs from lists of arcs,
and defines a structure read in another order of its words.

## Main definitions

* `Digraph.ofArcs`: the digraph with the listed arcs.
* `Graph L V`: a digraph with a relation on each arc; `Graph.ofArcs` builds one from
  (head, dependent, relation) triples, and `Graph.rel r` is its digraph of arcs bearing `r`.
* `Digraph.linearize`, `Digraph.mirror`, and `Graph.comap`, `Graph.linearize`: a structure read
  in another order of its positions.

## Implementation notes

A structure carries no words: the words of a sentence are a function on its positions, held
beside the graph by whatever reads them. It carries no root either. A tree is an arborescence
`G.IsArborescence r`, whose root the digraph determines.

`Graph L V` extends `Digraph V`, so the notions defined on digraphs apply to a labelled graph by
dot notation. Its adjacency is that of having a label; `Graph.ofLabel` is the constructor.
Positions are 0-indexed; CoNLL-U is 1-indexed with `0` as an artificial root.

## References

* [melcuk-1988]
* [kuhlmann-nivre-2006]
* [de-marneffe-nivre-2019]
-/

@[expose] public section

/-! ### Digraphs from arcs, and their linearizations -/

namespace Digraph

variable {V : Type*} {n : ℕ}

/-- The digraph whose arcs are the listed pairs, each of a head and one of its dependents. -/
def ofArcs [DecidableEq V] (arcs : List (V × V)) : Digraph V where
  Adj v w := (v, w) ∈ arcs

@[simp] theorem ofArcs_adj [DecidableEq V] {arcs : List (V × V)} {v w : V} :
    (ofArcs arcs).Adj v w ↔ (v, w) ∈ arcs := Iff.rfl

instance [DecidableEq V] (arcs : List (V × V)) : DecidableRel (ofArcs arcs).Adj :=
  fun v w ↦ inferInstanceAs (Decidable ((v, w) ∈ arcs))

/-- The permutation of the positions given by a listing of them in a new order, sending the new
position `p` to the old position `order[p]`. -/
def orderPerm (order : List (Fin n)) (h : order.Perm (List.finRange n)) : Equiv.Perm (Fin n) :=
  (finCongr (h.length_eq.trans List.length_finRange).symm).trans
    ((h.nodup_iff.mpr (List.nodup_finRange n)).getEquivOfForallMemList order
      fun x ↦ h.mem_iff.mpr (List.mem_finRange x))

/-- The digraph read in the order `order`, which lists every position once. The word at position `p`
is the word of `G` at `order[p]`, and the arcs follow the words. -/
def linearize (G : Digraph (Fin n)) (order : List (Fin n)) (h : order.Perm (List.finRange n)) :
    Digraph (Fin n) :=
  G.comap (orderPerm order h)

instance (G : Digraph (Fin n)) [DecidableRel G.Adj] (order : List (Fin n))
    (h : order.Perm (List.finRange n)) : DecidableRel (G.linearize order h).Adj :=
  inferInstanceAs (DecidableRel (G.comap _).Adj)

/-- The mirror image of a digraph on positions, read from the last word to the first. -/
def mirror (G : Digraph (Fin n)) : Digraph (Fin n) := G.comap Fin.rev

@[simp] theorem mirror_adj (G : Digraph (Fin n)) (v w : Fin n) :
    G.mirror.Adj v w ↔ G.Adj v.rev w.rev := Iff.rfl

instance (G : Digraph (Fin n)) [DecidableRel G.Adj] : DecidableRel G.mirror.Adj :=
  inferInstanceAs (DecidableRel (G.comap _).Adj)

@[simp] theorem mirror_mirror (G : Digraph (Fin n)) : G.mirror.mirror = G :=
  Digraph.ext (by ext; simp)

theorem mirror_involutive : Function.Involutive (mirror (n := n)) := mirror_mirror

end Digraph

/-! ### Labelled graphs -/

namespace Dependency

/-- A dependency graph on the vertices `V` with relations in `L` is a digraph each of whose arcs
carries a relation. -/
structure Graph (L V : Type*) extends Digraph V where
  /-- The relation of the arc from head `v` to dependent `w`, if there is an arc. -/
  label : V → V → Option L
  /-- The arcs are the pairs that carry a relation. -/
  adj_iff_isSome (v w : V) : Adj v w ↔ (label v w).isSome

namespace Graph

variable {L V W : Type*} {n : ℕ} (g : Graph L V)

/-- The dependency graph with the given partial labelling of pairs of vertices. -/
def ofLabel (label : V → V → Option L) : Graph L V where
  Adj v w := (label v w).isSome
  label := label
  adj_iff_isSome _ _ := Iff.rfl

@[simp] theorem label_ofLabel (label : V → V → Option L) : (ofLabel label).label = label := rfl

instance : DecidableRel g.Adj := fun _ _ ↦ decidable_of_iff _ (g.adj_iff_isSome _ _).symm

theorem adj_iff_exists_label {g : Graph L V} {v w : V} : g.Adj v w ↔ ∃ r, g.label v w = some r :=
  (g.adj_iff_isSome v w).trans Option.isSome_iff_exists

theorem ext_label {g h : Graph L V} (e : g.label = h.label) : g = h := by
  obtain ⟨⟨a⟩, l, hl⟩ := g
  obtain ⟨⟨a'⟩, l', hl'⟩ := h
  obtain rfl : l = l' := e
  obtain rfl : a = a' := funext₂ fun v w ↦ propext ((hl v w).trans (hl' v w).symm)
  rfl

/-- The arcs of a graph that bear the relation `r`. -/
def rel (r : L) : Digraph V where
  Adj v w := g.label v w = some r

instance [DecidableEq L] (r : L) : DecidableRel (g.rel r).Adj :=
  fun v w ↦ inferInstanceAs (Decidable (g.label v w = some r))

theorem rel_le (r : L) : g.rel r ≤ g.toDigraph := fun _ _ h ↦ adj_iff_exists_label.2 ⟨r, h⟩

/-- The partial labelling given by a list of (head, dependent, relation) triples, the first
triple for a pair deciding its relation. -/
def arcsLabel [DecidableEq V] (arcs : List (V × V × L)) (v w : V) : Option L :=
  (arcs.find? fun a ↦ a.1 == v && a.2.1 == w).map (·.2.2)

theorem arcsLabel_isSome_iff [DecidableEq V] {arcs : List (V × V × L)} {v w : V} :
    (arcsLabel arcs v w).isSome ↔ ∃ r, (v, w, r) ∈ arcs := by
  simp only [arcsLabel, Option.isSome_map, List.find?_isSome, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, b, r⟩, hmem, rfl, rfl⟩
    exact ⟨r, hmem⟩
  · rintro ⟨r, hmem⟩
    exact ⟨(v, w, r), hmem, rfl, rfl⟩

/-- The dependency graph with the listed arcs, each a (head, dependent, relation) triple. Later
triples for the same pair are ignored. -/
def ofArcs [DecidableEq V] (arcs : List (V × V × L)) : Graph L V := ofLabel (arcsLabel arcs)

@[simp] theorem ofArcs_adj [DecidableEq V] {arcs : List (V × V × L)} {v w : V} :
    (ofArcs arcs).Adj v w ↔ ∃ r, (v, w, r) ∈ arcs := arcsLabel_isSome_iff

/-- The pullback of a dependency graph along a function of vertices, relations following
arcs. -/
def comap (f : W → V) (g : Graph L V) : Graph L W where
  toDigraph := g.toDigraph.comap f
  label v w := g.label (f v) (f w)
  adj_iff_isSome v w := g.adj_iff_isSome (f v) (f w)

@[simp] theorem label_comap (f : W → V) (v w : W) :
    (g.comap f).label v w = g.label (f v) (f w) := rfl

@[simp] theorem toDigraph_comap (f : W → V) : (g.comap f).toDigraph = g.toDigraph.comap f := rfl

/-- The dependency graph read in the order `order`, as `Digraph.linearize`. -/
def linearize (g : Graph L (Fin n)) (order : List (Fin n)) (h : order.Perm (List.finRange n)) :
    Graph L (Fin n) :=
  g.comap (Digraph.orderPerm order h)

@[simp] theorem toDigraph_linearize (g : Graph L (Fin n)) (order : List (Fin n))
    (h : order.Perm (List.finRange n)) :
    (g.linearize order h).toDigraph = g.toDigraph.linearize order h :=
  g.toDigraph_comap _

end Graph

end Dependency
