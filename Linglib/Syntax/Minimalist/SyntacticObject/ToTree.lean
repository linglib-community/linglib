/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Tree.Basic

/-!
# Planar syntactic objects as constituency trees

The constituency tree of a planar syntactic object is its ordered tree with the vertices
relabelled: a lexical item becomes a terminal, an unlabelled vertex a projection, and a trace a
trace with an index. The tree has the object's positions, so whatever is stated on positions,
c-command among them, carries over by the lemmas about relabelling a tree
(`RoseTree.cCommands_map`), and it [pronounces the object's tokens in order](##yield_toTree). The
type-driven composition engine, binding configurations and the spans of prosodic constituency read
a Minimalist object through this tree.

## Implementation notes

* Categories are `Unit`. The engine, c-command and the yield ignore categories; the categories a
  head function assigns (`Minimalist.lexicalHeadAt`) depend on the position, not on the vertex, and
  are not a relabelling.
* A constituency tree has traces and binders only, so a copy is not represented, and no binder is
  introduced: a trace is free in the tree, interpreted by the assignment. The index of a trace is
  a parameter, `traceIndex` being the choice that keeps the index-free trace apart from the trace
  of every token.

## References

* [heim-kratzer-1998]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open PhraseStructure Core.Order

/-- The index of a trace by the token it is the trace of: `0` for the index-free trace and the
token's identifier plus one otherwise, so that no token's trace shares the index-free trace's. -/
def traceIndex : Option LexicalItem.Token → ℕ
  | none => 0
  | some a => a.id + 1

namespace SyntacticObject

variable {L : Type}

/-- The label of a vertex in a constituency tree: a lexical item is a terminal, the unlabelled
vertex a projection, and a trace the trace of the index `τ` gives it. -/
def Vertex.toLabel (τ : Option L → ℕ) : Vertex L → Tree.Label Unit L
  | Vertex.lex a => .terminal () a
  | Vertex.bare => .phrase () .projection
  | .inr o => .trace (τ o) ()

end SyntacticObject

namespace PlanarSyntacticObject

variable {L : Type} (τ : Option L → ℕ)

/-- The constituency tree of a planar object, its ordered tree relabelled, a trace having the
index `τ` gives it. -/
def toTree (t : PlanarSyntacticObject L) : Tree Unit L :=
  t.toRoseTree.map (SyntacticObject.Vertex.toLabel τ)

/-- The tree pronounces the object's tokens, in order. -/
theorem yield_toTree (t : PlanarSyntacticObject L) : (t.toTree τ).yield = t.yield := by
  simp only [toTree, Tree.yield, Tree.terminals, RoseTree.leafList_map, yield,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext v
  rcases v with (_ | _) | (_ | _) <;> rfl

end PlanarSyntacticObject

end Minimalist
