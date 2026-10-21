/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Phonology.OptimalityTheory.Constraint.Alignment
public import Linglib.Core.Data.RoseTree.Span

/-!
# Match Theory

This file defines the Match constraints of the syntax–prosody interface. A constituent structure
over a string is the family of spans its constituents cover, so a syntactic input enters as the
spans of its constituents of a category, counted in the syllables of the output, and a prosodic
candidate as the spans of its nodes at a level. Match(α, π) requires each α-span to be the span
of a π-node and Match(π, α) each π-span to be an α-span: two-sided alignment, both edges of a
constituent coinciding with those of one constituent of the other category. One-sided alignment is
`Constraint.alignLeft` and `Constraint.alignRight` on the same families.

## Main definitions

* `Prosody.levelSpans`: the spans of the nodes of a prosodic tree at a level.
* `Prosody.syntaxProsodyMatch`, `Prosody.prosodySyntaxMatch`: Match(α, π) and Match(π, α).

## Implementation notes

The syntactic family is a list of spans rather than a tree, so the constraints read any syntactic
representation, a phrase-structure tree or a morphological word, once the spans of its
constituents are given in the syllables of the output. The list keeps multiplicity, so a φ
recursively over a φ of the same span is counted twice.

## References

* [selkirk-2011]
* [ito-mester-2019]
-/

@[expose] public section

namespace Prosody

open OptimalityTheory

/-- The spans of the `ℓ`-nodes of a prosodic tree, the span counterpart of `levelPositions`. -/
abbrev levelSpans (ℓ : Level) (t : Tree) : List (ℕ × ℕ) := t.spans (·.value.level = ℓ)

/-- **Match(α, π)** ([selkirk-2011]): one violation for each span of the syntactic family `α` that
is the span of no `π`-node, the two edges of the constituent coinciding with those of no
`π`-node ([ito-mester-2019]). -/
def syntaxProsodyMatch (α : List (ℕ × ℕ)) (π : Level) : Constraint Tree :=
  (Constraint.align Eq).comap fun t ↦ (α, levelSpans π t)

/-- **Match(π, α)** ([selkirk-2011]): one violation for each `π`-node whose span is the span of no
constituent of the syntactic family `α`. -/
def prosodySyntaxMatch (π : Level) (α : List (ℕ × ℕ)) : Constraint Tree :=
  (Constraint.align Eq).comap fun t ↦ (levelSpans π t, α)

-- Two words phrased together: the φ over both matches the phrase spanning them, and neither word
-- is matched by a φ of its own.
example : prosodySyntaxMatch .ph [(0, 2)] (.ph [.om [.σ], .om [.σ]]) = 0 := by decide
example : syntaxProsodyMatch [(0, 1), (1, 2)] .ph (.ph [.om [.σ], .om [.σ]]) = 2 := by decide

end Prosody
