/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Workspaces

A workspace is a forest, a finite multiset, of syntactic objects. The forest product is disjoint
union with unit the empty forest, so a workspace is exactly what `of'` lifts into the Hopf algebra
`ConnesKreimer ℤ (UnorderedTree Vertex)`, on which the Merge operator of `Workspace/Algebra/` acts.

## Main definitions

* `Minimalist.Workspace`: forests of syntactic objects.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.1)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-- A workspace is a forest of syntactic objects. -/
abbrev Workspace : Type := Forest SyntacticObject

end Minimalist
