/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# Planar syntactic objects as constituency trees

The constituency tree of a planar syntactic object is its ordered tree with the vertices
relabelled: an item becomes a terminal and an unlabelled vertex a projection. The tree has the
object's positions, so whatever is stated on positions, c-command among them, carries over by the
lemmas about relabelling a tree (`RoseTree.cCommands_map`), and it [has the object's items in
order](##yield_toTree). The type-driven composition engine, binding configurations and the spans
of prosodic constituency read a Minimalist object through this tree.

## Implementation notes

* Categories are `Unit`. The engine, c-command and the yield ignore categories; the categories a
  head function assigns (`Minimalist.lexicalHeadAt`) depend on the position, not on the vertex, and
  are not a relabelling.
* The tree has no traces and no binders: a copy of a term is the term again at another vertex.

## References

* [heim-kratzer-1998]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open PhraseStructure

namespace SyntacticObject

variable {L : Type}

/-- The label of a vertex in a constituency tree: an item is a terminal and the unlabelled vertex
a projection. -/
def vertexLabel : Option L → Tree.Label Unit L
  | some a => .terminal () a
  | none => .phrase () .projection

end SyntacticObject

namespace PlanarSyntacticObject

variable {L : Type}

/-- The constituency tree of a planar object, its ordered tree relabelled. -/
def toTree (t : PlanarSyntacticObject L) : Tree Unit L :=
  t.toRoseTree.map SyntacticObject.vertexLabel

/-- The tree has the object's items, in order. -/
theorem yield_toTree (t : PlanarSyntacticObject L) : t.toTree.yield = t.yield := by
  simp only [toTree, Tree.yield, Tree.terminals, RoseTree.leafList_map, yield,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext v
  rcases v with _ | _ <;> rfl

end PlanarSyntacticObject

end Minimalist
