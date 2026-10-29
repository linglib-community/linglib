/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Linglib.Morphology.Word.Basic

/-!
# Dependency graphs

This file defines the dependency structure of a sentence: the vertices are
the sentence positions `Fin n` with their linear order, and the arcs are a
partial labeling of ordered position pairs by labels of a type `L`. The
labels are a framework's relations, such as the Universal Dependencies
relations `UD.DepRel`, or `Unit` for an unlabeled graph. A distinguished
`root` position replaces CoNLL-U's artificial root token.

Well-formedness (`Graph.IsTree`) is defined in `Dominance.lean`, beside
the dominance relation it is stated through.

## Main definitions

* `Graph L n` is a dependency graph on `n` words: a token at every position,
  an optional label on every ordered pair of positions (head to
  dependent), and a root position.
* `Graph.toDigraph` and `Graph.toSimpleGraph` are the directed and
  undirected views of a graph as mathlib's graph carriers.
* `Graph.enhance` adds arcs to a graph, as in UD's *enhanced*
  representation; `HasUnrepresentedArg` says that an enhanced graph gives
  a position an argument relation its basic graph lacks.

## Implementation notes

Positions are 0-indexed; CoNLL-U is 1-indexed with `0` as an artificial
root, so wire-format conversion shifts indices.

`label` returns at most one relation per ordered pair, faithful to
dependency trees and basic UD. If an enhanced-UD fixture ever needs
parallel arcs on one pair, the field generalizes to a list. Feature-level
constraints (agreement) are `Syntax/Agreement/`'s domain, not the
carrier's.

## References

[melcuk-1988] — Dependency syntax: theory and practice, source of the
arcs-among-ordered-words presentation
[kuhlmann-nivre-2006] — Mildly non-projective dependency structures,
source of the root convention
[kuhlmann-2013] — Mildly non-projective dependency grammar
[de-marneffe-nivre-2019] — Dependency grammar, on UD's enhanced
representation
-/

@[expose] public section

open Morphology (Word)

namespace DependencyGrammar

/-! ### Dependency graphs -/

/-- A dependency graph on `n` words: the sentence's tokens as a labeling of
the positions `Fin n`, the arcs as a partial labeling of ordered position
pairs (head → dependent) by labels of `L`, and a distinguished root
position. -/
@[ext]
structure Graph (L : Type*) (n : ℕ) where
  /-- The token at each position. -/
  words : Fin n → Word
  /-- The label of the arc from head `v` to dependent `w`, if there is an arc. -/
  label : Fin n → Fin n → Option L
  /-- The root position. -/
  root : Fin n

namespace Graph

variable {L : Type*} {n : ℕ} (g : Graph L n)

/-- Adjacency: there is an arc from head `v` to dependent `w`. -/
def Adj (v w : Fin n) : Prop := (g.label v w).isSome

instance : DecidableRel g.Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ = true))

theorem adj_iff_exists {g : Graph L n} {v w : Fin n} :
    g.Adj v w ↔ ∃ r, g.label v w = some r := Option.isSome_iff_exists

/-- Positions linked by an arc in either direction — the undirected view of
adjacency. -/
def Linked (a b : Fin n) : Prop := g.Adj a b ∨ g.Adj b a

instance (a b : Fin n) : Decidable (g.Linked a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Linked.symm {g : Graph L n} {a b : Fin n} (h : g.Linked a b) :
    g.Linked b a := Or.symm h

/-! ### Views onto mathlib's graph carriers -/

/-- The graph as a mathlib `Digraph` on positions. -/
def toDigraph : Digraph (Fin n) := ⟨g.Adj⟩

@[simp] theorem toDigraph_adj (v w : Fin n) : g.toDigraph.Adj v w ↔ g.Adj v w :=
  Iff.rfl

/-- The graph's undirected view: mathlib's orientation-forgetting
`Digraph.toSimpleGraphInclusive` applied to `toDigraph`. Planarity and
catena connectivity are stated through it. -/
def toSimpleGraph : SimpleGraph (Fin n) := g.toDigraph.toSimpleGraphInclusive

@[simp] theorem toSimpleGraph_adj (v w : Fin n) :
    g.toSimpleGraph.Adj v w ↔ v ≠ w ∧ g.Linked v w := Iff.rfl

instance : DecidableRel g.toSimpleGraph.Adj :=
  fun v w ↦ decidable_of_iff _ (g.toSimpleGraph_adj v w).symm

theorem toSimpleGraph_adj_of_ne {g : Graph L n} {v w : Fin n} (h : v ≠ w) :
    g.toSimpleGraph.Adj v w ↔ g.Linked v w := by simp [h]

/-! ### Heads and dependents -/

/-- The head positions of `w`. -/
def parents (w : Fin n) : Finset (Fin n) := {v | g.Adj v w}

/-- The dependent positions of `v`. -/
def children (v : Fin n) : Finset (Fin n) := {w | g.Adj v w}

@[simp] theorem mem_parents {g : Graph L n} {v w : Fin n} :
    v ∈ g.parents w ↔ g.Adj v w := by simp [parents]

@[simp] theorem mem_children {g : Graph L n} {v w : Fin n} :
    w ∈ g.children v ↔ g.Adj v w := by simp [children]

/-- The arcs as pairs of a head and a dependent position, forgetting their labels. -/
def arcs : Finset (Fin n × Fin n) := {p | g.Adj p.1 p.2}

@[simp] theorem mem_arcs {g : Graph L n} {p : Fin n × Fin n} : p ∈ g.arcs ↔ g.Adj p.1 p.2 := by
  simp [arcs]

/-! ### Constructors -/

/-- The partial label function induced by a CoNLL-U-style arc list of
(head, dependent, relation) triples. First match wins. -/
def arcsLabel (arcs : List (Fin n × Fin n × L)) (v w : Fin n) : Option L :=
  (arcs.find? fun a ↦ a.1 == v && a.2.1 == w).map (·.2.2)

theorem arcsLabel_isSome_iff {arcs : List (Fin n × Fin n × L)}
    {v w : Fin n} : (arcsLabel arcs v w).isSome ↔ ∃ r, (v, w, r) ∈ arcs := by
  simp only [arcsLabel, Option.isSome_map, List.find?_isSome, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨⟨a, b, r⟩, hmem, rfl, rfl⟩
    exact ⟨r, hmem⟩
  · rintro ⟨r, hmem⟩
    exact ⟨(v, w, r), hmem, rfl, rfl⟩

/-- Build a graph from CoNLL-U-style data: the token list (whose length
fixes `n`), the root position, and the arcs as
(head, dependent, relation) triples. Later arcs for the same pair are
ignored. -/
def ofArcs (words : List Word) (root : Fin words.length)
    (arcs : List (Fin words.length × Fin words.length × L)) :
    Graph L words.length :=
  { words := words.get, label := arcsLabel arcs, root }

@[simp] theorem ofArcs_adj {words : List Word} {root : Fin words.length}
    {arcs : List (Fin words.length × Fin words.length × L)}
    {v w : Fin words.length} :
    (ofArcs words root arcs).Adj v w ↔ ∃ r, (v, w, r) ∈ arcs :=
  arcsLabel_isSome_iff

/-- Add arcs to a graph (existing labels win), as in UD's *enhanced*
representation: semantic relations the single-headed tree cannot
encode — shared dependents in coordination, controlled subjects,
relative-clause gaps — become explicit arcs. -/
def enhance (extra : List (Fin n × Fin n × L)) : Graph L n :=
  { g with label := fun v w ↦ g.label v w <|> arcsLabel extra v w }

@[simp] theorem enhance_adj {g : Graph L n}
    {extra : List (Fin n × Fin n × L)} {v w : Fin n} :
    (g.enhance extra).Adj v w ↔ g.Adj v w ∨ ∃ r, (v, w, r) ∈ extra := by
  cases h : g.label v w with
  | some r => simp [Adj, enhance, h]
  | none => simpa [Adj, enhance, h] using arcsLabel_isSome_iff

end Graph

/-- Position `w` has an argument relation in the enhanced graph that the
basic graph fails to encode. -/
def HasUnrepresentedArg {L : Type*} {n : ℕ} (basic enhanced : Graph L n) (w : Fin n) : Prop :=
  ∃ v, enhanced.Adj v w ∧ ¬ basic.Adj v w

instance {L : Type*} {n : ℕ} (b e : Graph L n) (w : Fin n) :
    Decidable (HasUnrepresentedArg b e w) :=
  inferInstanceAs (Decidable (∃ _, _))

theorem hasUnrepresentedArg_enhance {L : Type*} {n : ℕ} (g : Graph L n) {x w : Fin n} (r : L)
    (extra : List (Fin n × Fin n × L)) (hmem : (x, w, r) ∈ extra) (h : ¬ g.Adj x w) :
    HasUnrepresentedArg g (g.enhance extra) w :=
  ⟨x, Graph.enhance_adj.mpr (Or.inr ⟨r, hmem⟩), h⟩

end DependencyGrammar
