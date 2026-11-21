/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Hierarchy
public import Linglib.Phonology.OptimalityTheory.Correspondence.Alignment
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.RoseTree.Span

/-!
# Match Theory

This file defines the Match constraints of the syntax–prosody interface ([selkirk-2011]). A
constituent structure over a string is the family of spans its constituents cover, so a syntactic
input enters as the spans of its constituents of a category, counted in the syllables of the
output, and a prosodic candidate as the spans of its nodes at a level. Match(α, π) requires each
α-span to be the span of a π-node and Match(π, α) each π-span to be an α-span: MAX and DEP of the
relation of having the same span, both edges of a constituent coinciding with those of one
constituent of the other category. One-sided alignment is MAX or DEP of
`Correspondence.ofEdges` on the same families.

## Implementation notes

The syntactic family is a list of spans rather than a tree, so the constraints read any syntactic
representation, a phrase-structure tree or a morphological word, once the spans of its
constituents are given in the syllables of the output. A span is a `NonemptyInterval ℕ` of cuts
of the frontier, as `RoseTree.spans` gives them, so that a constituent within another is `≤` and
a span counted in words is carried to syllables by `NonemptyInterval.map (cut l)`. The list keeps
multiplicity, so a φ recursively over a φ of the same span is counted twice.

## References

* [selkirk-2011]
* [ito-mester-2019]
-/

@[expose] public section

namespace Prosody

open OptimalityTheory

/-- The spans of the `ℓ`-nodes of a prosodic tree, the span counterpart of `levelPositions`. -/
abbrev levelSpans {M : Type*} (ℓ : Level) (t : RoseTree (Constituent Level M)) :
    List (NonemptyInterval ℕ) :=
  t.spans (·.value.level = ℓ)

/-- The cut of the frontier before the `i`th of consecutive units of the sizes `l`, monotone in
`i`: it carries a span counted in words or terminals to the span counted in their syllables. -/
def cut (l : List ℕ) : ℕ →o ℕ :=
  ⟨fun i ↦ (l.take i).sum, fun _ _ h ↦
    (List.take_sublist_take_left h).sum_le_sum fun _ _ ↦ Nat.zero_le _⟩

@[simp] theorem cut_apply (l : List ℕ) (i : ℕ) : cut l i = (l.take i).sum := rfl

/-- **Match(α, π)** ([selkirk-2011]): one violation for each span of the syntactic family `α` that
is the span of no `π`-node, the two edges of the constituent coinciding with those of no
`π`-node ([ito-mester-2019]). -/
def syntaxProsodyMatch {M : Type*} (α : List (NonemptyInterval ℕ)) (π : Level) :
    Constraint (RoseTree (Constituent Level M)) :=
  fun t ↦ (Correspondence.ofRel Eq α.get (levelSpans π t).get).maxViol

/-- **Match(π, α)** ([selkirk-2011]): one violation for each `π`-node whose span is the span of no
constituent of the syntactic family `α`. -/
def prosodySyntaxMatch {M : Type*} (π : Level) (α : List (NonemptyInterval ℕ)) :
    Constraint (RoseTree (Constituent Level M)) :=
  fun t ↦ (Correspondence.ofRel Eq α.get (levelSpans π t).get).depViol

-- Two words phrased together: the φ over both matches the phrase spanning them, and neither word
-- is matched by a φ of its own.
example : prosodySyntaxMatch .ph [⟨(0, 2), by decide⟩] (Tree.ph [.om [.σ], .om [.σ]]) = 0 := by
  decide
example : syntaxProsodyMatch [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩] .ph
    (Tree.ph [.om [.σ], .om [.σ]]) = 2 := by
  decide
end Prosody
