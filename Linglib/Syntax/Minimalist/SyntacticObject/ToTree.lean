/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Tree.Basic

/-!
# Linearized syntactic objects as constituency trees

A linearized syntactic object is a rose tree over vertices, so relabelling its vertices gives a
constituency tree with the same shape: a lexical leaf becomes a terminal, the bare label of an
internal node a projection, and a trace a trace. The positions, and so the branching nodes, are
the object's, so the tree [pronounces the object's tokens in order](##yield_toTree) and its
c-command is [the object's](##cCommands_toTree_iff), which is c-command between the terms at those
positions when the commander's term occurs once ([its terms](##cCommands_termAt_iff_toTree)).
Whatever reads a constituency tree, the type-driven composition engine, binding configurations
and the spans of prosodic constituency, then reads a Minimalist object.

## Implementation notes

* Categories are `Unit`. The engine, c-command and the yield ignore categories; the categories a
  head function assigns (`Minimalist.lexicalHeadAt`) depend on the position, not on the vertex, and
  are not a relabelling.
* A constituency tree has traces and binders only, so a copy is not represented. A trace of a
  token is a trace whose index the token gives, and the index-free trace has index `0`. No binder is
  introduced: a trace is free in the tree, interpreted by the assignment.

## References

* [heim-kratzer-1998]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open PhraseStructure Core.Order

namespace SyntacticObject

variable {L : Type}

/-- The label of a vertex in a constituency tree: a lexical leaf is a terminal, the bare label a
projection, the trace of a token the trace of index `ι` of the token, and the index-free trace the
trace of index `0`. -/
def Vertex.toLabel (ι : L → ℕ) : Vertex L → Tree.Label Unit L
  | .inl (some a) => .terminal () a
  | .inl none => .phrase () .projection
  | .inr (some a) => .trace (ι a) ()
  | .inr none => .trace 0 ()

end SyntacticObject

namespace LinearizedSyntacticObject

variable {L : Type} (ι : L → ℕ)

/-- The constituency tree of a linearized object, with the trace of a token indexed by `ι` and
the index-free trace by `0`. -/
def toTree (t : LinearizedSyntacticObject L) : Tree Unit L :=
  t.val.map (SyntacticObject.Vertex.toLabel ι)

@[simp] theorem toTree_leaf (a : L) : (leaf a).toTree ι = .terminal () a := rfl

@[simp] theorem toTree_traceOf (a : L) : (traceOf a).toTree ι = .trace (ι a) () := rfl

@[simp] theorem toTree_trace : (trace : LinearizedSyntacticObject L).toTree ι = .trace 0 () := rfl

@[simp] theorem toTree_merge (l r : LinearizedSyntacticObject L) :
    (merge l r).toTree ι = .phrase () .projection [l.toTree ι, r.toTree ι] := rfl

/-- The tree pronounces the object's tokens, in order. -/
theorem yield_toTree (t : LinearizedSyntacticObject L) : (t.toTree ι).yield = t.yield := by
  simp only [toTree, Tree.yield, Tree.terminals, RoseTree.leafList_map, yield,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext v
  rcases v with (_ | _) | (_ | _) <;> rfl

/-- C-command in the tree is c-command between the positions of the object. -/
theorem cCommands_toTree_iff (t : LinearizedSyntacticObject L) (a b : TreePath) :
    RoseTree.CCommands (t.toTree ι) a b ↔ t.val.CCommands a b :=
  RoseTree.cCommands_map _ _ a b

/-- When the term at `a` occurs once, the terms it c-commands are those at the positions that `a`
c-commands in the tree. -/
theorem cCommands_termAt_iff_toTree {t : LinearizedSyntacticObject} (ι : LexicalItem.Token → ℕ)
    {a : t.val.Positions} {x : SyntacticObject} (hu : ∀ q, t.termAt q = t.termAt a → q = a) :
    t.toSyntacticObject.CCommands (t.termAt a) x ↔
      ∃ q : t.val.Positions, RoseTree.CCommands (t.toTree ι) a q ∧ t.termAt q = x := by
  simp only [cCommands_toTree_iff]
  exact cCommands_termAt_iff hu

end LinearizedSyntacticObject

end Minimalist
