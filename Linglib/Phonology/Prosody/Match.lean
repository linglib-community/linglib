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
`Constraint.alignLeft` and `Constraint.alignRight` on the same families. MAX(α, π) asks only that
each α-constituent have a corresponding π-node, one containing its head and no head from outside
it, no π-node answering to two α-constituents.

## Main definitions

* `Prosody.levelSpans`: the spans of the nodes of a prosodic tree at a level.
* `Prosody.Corresponds`: a node corresponds to a constituent, containing its head and no foreign
  head.
* `Prosody.syntaxProsodyMatch`, `Prosody.prosodySyntaxMatch`: Match(α, π) and Match(π, α).
* `Prosody.syntaxProsodyMax`: MAX(α, π), existential correspondence.

## Main results

* `Prosody.deficiency_corresponds_le`: MAX(α, π) asks no more than Match(α, π).

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

/-- A node of span `p` **corresponds** to the constituent `a` of the family `α`, given by its span
and the position of its head, when it contains the head of `a` and no head of `α` lying outside
`a` ([ito-mester-2019]). -/
abbrev Corresponds (α : List ((ℕ × ℕ) × ℕ)) (a : (ℕ × ℕ) × ℕ) (p : ℕ × ℕ) : Prop :=
  a.2 ∈ Set.Ico p.1 p.2 ∧ ∀ b ∈ α, b.2 ∈ Set.Ico p.1 p.2 → b.2 ∈ Set.Ico a.1.1 a.1.2

/-- **MAX(α, π)** ([ito-mester-2019]): one violation for each constituent of the family `α`, given
by its span and the position of its head, left without a corresponding `π`-node by the best
correspondence in which no `π`-node answers to two constituents. A `π`-node over two sister
constituents answers to neither, and a constituent and its subconstituents need a `π`-node
each. -/
def syntaxProsodyMax (α : List ((ℕ × ℕ) × ℕ)) (π : Level) : Constraint Tree :=
  (Constraint.deficiency (Corresponds α)).comap fun t ↦ (α, levelSpans π t)

variable {α : List ((ℕ × ℕ) × ℕ)}

/-- **Existential correspondence asks no more than Match** ([ito-mester-2019]): where the
constituents of `α` have distinct spans each containing its head, fewer of them lack a
corresponding node than lack a node of the same span. -/
theorem deficiency_corresponds_le (hα : (α.map (·.1)).Nodup)
    (hhead : ∀ a ∈ α, a.2 ∈ Set.Ico a.1.1 a.1.2) (m : List (ℕ × ℕ)) :
    Constraint.deficiency (Corresponds α) (α, m) ≤ Constraint.align Eq (α.map (·.1), m) := by
  have h := Constraint.deficiency_le_align (R := Corresponds α) (S := fun a p ↦ a.1 = p)
    (x := (α, m)) (List.Nodup.of_map _ hα) (fun a ha p hp ↦ hp ▸ ⟨hhead a ha, fun _ _ ↦ id⟩)
    fun a ha a' ha' p h h' ↦ List.inj_on_of_nodup_map hα ha ha' (h.trans h'.symm)
  simpa [Constraint.align, List.countP_map, Function.comp_def] using h

-- Two words phrased together: the φ over both matches the phrase spanning them, and neither word
-- is matched by a φ of its own.
example : prosodySyntaxMatch .ph [(0, 2)] (.ph [.om [.σ], .om [.σ]]) = 0 := by decide
example : syntaxProsodyMatch [(0, 1), (1, 2)] .ph (.ph [.om [.σ], .om [.σ]]) = 2 := by decide
-- Two sister phrases share no corresponding φ when phrased together, and each has its own when
-- phrased apart. A φ over T serves only one of the two projections T heads, so the higher one
-- needs a φ of its own.
example : syntaxProsodyMax [((0, 1), 0), ((1, 2), 1)] .ph (.ph [.om [.σ], .om [.σ]]) = 2 := by
  decide
example : syntaxProsodyMax [((0, 1), 0), ((1, 2), 1)] .ph (.ph [.ph [.om [.σ]], .ph [.om [.σ]]])
    = 0 := by
  decide
example : syntaxProsodyMax [((0, 2), 1), ((0, 1), 0), ((1, 2), 1)] .ph
    (.node .iota [Tree.ph [.om [.σ]], Tree.ph [.om [.σ]]]) = 1 := by
  decide

end Prosody
