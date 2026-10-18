/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Replace
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Substitution on syntactic objects

`SyntacticObject.replace s target replacement` substitutes every subterm of `s` equal to
`target` by `replacement`; it is `UnorderedTree.replace` closed under well-formedness, which holds
because substitution preserves the arity of every vertex. The copy-theory use is
`s.replace mover trace`, leaving a trace where a mover was. This is a structural operation:
the Merge-algebraic Internal Merge is the coproduct composition of `Merge/Internal.lean`, with
traces as cut remainders and chains held at the workspace level, and `replace` supports the
transformational view that study files are written in. It is noncomputable; concrete cases
reduce by `replace_self`, `replace_merge_of_ne`, and the leaf lemmas.

## Main definitions

* `Minimalist.SyntacticObject.replace`
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-- Substitution preserves well-formedness. -/
theorem isSyntacticObject_replace (target replacement s : SyntacticObject) :
    IsSyntacticObject (UnorderedTree.replace target.val replacement.val s.val) := by
  induction s using ind with
  | leaf tok =>
    rw [show (SyntacticObject.leaf tok).val = UnorderedTree.leaf (Vertex.lex tok) from rfl,
      UnorderedTree.replace_leaf]
    split
    · exact replacement.2
    · exact (SyntacticObject.leaf tok).2
  | trace =>
    rw [show trace.val = UnorderedTree.leaf (Sum.inr none) from rfl, UnorderedTree.replace_leaf]
    split
    · exact replacement.2
    · exact trace.2
  | traceOf tok =>
    rw [show (traceOf tok).val = UnorderedTree.leaf (Sum.inr (some tok)) from rfl,
      UnorderedTree.replace_leaf]
    split
    · exact replacement.2
    · exact (traceOf tok).2
  | merge l r ihl ihr =>
    rw [merge_val, UnorderedTree.replace_node_pair]
    split
    · exact replacement.2
    · exact (isSyntacticObject_merge_iff _ _).2 ⟨ihl, ihr⟩

namespace SyntacticObject

/-- Replace every subterm of `s` equal to `target` by `replacement`. -/
noncomputable def replace (s target replacement : SyntacticObject) : SyntacticObject :=
  ⟨UnorderedTree.replace target.val replacement.val s.val,
    isSyntacticObject_replace target replacement s⟩

@[simp] theorem replace_val (s target replacement : SyntacticObject) :
    (replace s target replacement).val
      = UnorderedTree.replace target.val replacement.val s.val := rfl

@[simp] theorem replace_self (target replacement : SyntacticObject) :
    replace target target replacement = replacement :=
  Subtype.ext (by rw [replace_val, UnorderedTree.replace_self])

/-- At a node other than the target, substitution recurses into both daughters. -/
theorem replace_merge_of_ne {l r target replacement : SyntacticObject} (h : merge l r ≠ target) :
    replace (merge l r) target replacement
      = merge (replace l target replacement) (replace r target replacement) := by
  apply Subtype.ext
  rw [replace_val, merge_val, UnorderedTree.replace_node_pair, ite_eq_right, merge_val, replace_val,
    replace_val]
  rw [← merge_val]
  exact fun heq => h (Subtype.ext heq)

/-- A leaf other than the target is kept. -/
theorem replace_of_val_eq_leaf {s target replacement : SyntacticObject} {a : Vertex}
    (hs : s.val = UnorderedTree.leaf a) (h : s ≠ target) : s.replace target replacement = s := by
  apply Subtype.ext
  rw [replace_val, hs, UnorderedTree.replace_leaf]
  split_ifs with hc
  · exact (h (Subtype.ext (hs.trans hc))).elim
  · rfl

/-- Moving the daughter `r` out of `[l r]` and leaving a trace yields `[l′ t]`, with `l′` the
    substituted left daughter; a tree is never its own daughter, taken here as a hypothesis. -/
example (l r : SyntacticObject) (h : merge l r ≠ r) :
    replace (merge l r) r trace = merge (replace l r trace) trace := by
  rw [replace_merge_of_ne h, replace_self]

end SyntacticObject

end Minimalist
