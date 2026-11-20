/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Tree.Basic

/-!
# Bracket notation for syntactic objects

`so%` writes a planar syntactic object in brackets, in the syntax of `tree%`: `[x y]` is the
Merge of `x` and `y`, a bare identifier `w` the leaf of the lexical token `w`, `⟨e⟩` the leaf of
the token `e`, and `(t)` the object `t`, such as a trace or a phrase built elsewhere. Brackets
carry no labels, since the label of a syntactic object is computed from its head.
-/

@[expose] public section

namespace Minimalist

/-- A planar syntactic object in bracket notation. -/
syntax "so%" phraseTree : term

macro_rules
  | `(so% $w:ident) => `(Minimalist.PlanarSyntacticObject.leaf $w)
  | `(so% ⟨$e⟩) => `(Minimalist.PlanarSyntacticObject.leaf $e)
  | `(so% ($t)) => `($t)
  | `(so% [$x $y]) => `(Minimalist.PlanarSyntacticObject.merge (so% $x) (so% $y))

end Minimalist
