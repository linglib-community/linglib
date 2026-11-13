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
* `Prosody.cut`: the monotone map from units to the syllable cuts before them.
* `Prosody.HeadedSpan`, `Prosody.Corresponds`: a constituent with its head, and a node
  corresponding to it, containing its head and no foreign head.
* `Prosody.syntaxProsodyMatch`, `Prosody.prosodySyntaxMatch`: Match(α, π) and Match(π, α).
* `Prosody.syntaxProsodyMax`: MAX(α, π), existential correspondence.

## Main results

* `Prosody.deficiency_corresponds_le`: MAX(α, π) asks no more than Match(α, π).

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
abbrev levelSpans (ℓ : Level) (t : Tree) : List (NonemptyInterval ℕ) :=
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
def syntaxProsodyMatch (α : List (NonemptyInterval ℕ)) (π : Level) : Constraint Tree :=
  (Constraint.align Eq).comap fun t ↦ (α, levelSpans π t)

/-- **Match(π, α)** ([selkirk-2011]): one violation for each `π`-node whose span is the span of no
constituent of the syntactic family `α`. -/
def prosodySyntaxMatch (π : Level) (α : List (NonemptyInterval ℕ)) : Constraint Tree :=
  (Constraint.align Eq).comap fun t ↦ (levelSpans π t, α)

/-- A syntactic constituent as correspondence reads it: the span it covers and the terminal that
heads it. -/
structure HeadedSpan where
  /-- The span of the constituent. -/
  span : NonemptyInterval ℕ
  /-- The index in the frontier of the terminal heading the constituent. -/
  head : ℕ
  deriving DecidableEq

/-- A node of span `p` **corresponds** to the constituent `a` of the family `α` when it contains
the head of `a` and no head of `α` lying outside `a` ([ito-mester-2019]). -/
abbrev Corresponds (α : List HeadedSpan) (a : HeadedSpan) (p : NonemptyInterval ℕ) : Prop :=
  a.head ∈ Set.Ico p.fst p.snd ∧
    ∀ b ∈ α, b.head ∈ Set.Ico p.fst p.snd → b.head ∈ Set.Ico a.span.fst a.span.snd

/-- **MAX(α, π)** ([ito-mester-2019]): one violation for each constituent of the family `α` left
without a corresponding `π`-node by the best correspondence in which no `π`-node answers to two
constituents. A `π`-node over two sister constituents answers to neither, and a constituent and
its subconstituents need a `π`-node each. -/
def syntaxProsodyMax (α : List HeadedSpan) (π : Level) : Constraint Tree :=
  (Constraint.deficiency (Corresponds α)).comap fun t ↦ (α, levelSpans π t)

variable {α : List HeadedSpan}

/-- **Existential correspondence asks no more than Match** ([ito-mester-2019]): where the
constituents of `α` have distinct spans each containing its head, fewer of them lack a
corresponding node than lack a node of the same span. -/
theorem deficiency_corresponds_le (hα : (α.map (·.span)).Nodup)
    (hhead : ∀ a ∈ α, a.head ∈ Set.Ico a.span.fst a.span.snd) (m : List (NonemptyInterval ℕ)) :
    Constraint.deficiency (Corresponds α) (α, m) ≤ Constraint.align Eq (α.map (·.span), m) := by
  have h := Constraint.deficiency_le_align (R := Corresponds α) (S := fun a p ↦ a.span = p)
    (x := (α, m)) (List.Nodup.of_map _ hα) (fun a ha p hp ↦ hp ▸ ⟨hhead a ha, fun _ _ ↦ id⟩)
    fun a ha a' ha' p h h' ↦ List.inj_on_of_nodup_map hα ha ha' (h.trans h'.symm)
  simpa [Constraint.align, List.countP_map, Function.comp_def] using h

-- Two words phrased together: the φ over both matches the phrase spanning them, and neither word
-- is matched by a φ of its own.
example : prosodySyntaxMatch .ph [⟨(0, 2), by decide⟩] (.ph [.om [.σ], .om [.σ]]) = 0 := by decide
example : syntaxProsodyMatch [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩] .ph
    (.ph [.om [.σ], .om [.σ]]) = 2 := by
  decide
-- Two sister phrases share no corresponding φ when phrased together, and each has its own when
-- phrased apart. A φ over T serves only one of the two projections T heads, so the higher one
-- needs a φ of its own.
example : syntaxProsodyMax [⟨⟨(0, 1), by decide⟩, 0⟩, ⟨⟨(1, 2), by decide⟩, 1⟩] .ph
    (.ph [.om [.σ], .om [.σ]]) = 2 := by
  decide
example : syntaxProsodyMax [⟨⟨(0, 1), by decide⟩, 0⟩, ⟨⟨(1, 2), by decide⟩, 1⟩] .ph
    (.ph [.ph [.om [.σ]], .ph [.om [.σ]]]) = 0 := by
  decide
example : syntaxProsodyMax
    [⟨⟨(0, 2), by decide⟩, 1⟩, ⟨⟨(0, 1), by decide⟩, 0⟩, ⟨⟨(1, 2), by decide⟩, 1⟩] .ph
    (.node .iota [Tree.ph [.om [.σ]], Tree.ph [.om [.σ]]]) = 1 := by
  decide

end Prosody
