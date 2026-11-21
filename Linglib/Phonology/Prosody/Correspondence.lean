/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Match
public import Linglib.Phonology.OptimalityTheory.Correspondence.Deficiency

/-!
# Syntax–prosody correspondence

[ito-mester-2019] replace the Match constraints by correspondence between syntactic constituents
and prosodic nodes. A node corresponds to a constituent when it contains the head of the
constituent and no head from outside it, and MAX(α, π) asks that each α-constituent have a
corresponding π-node, no π-node answering to two constituents. We define `Prosody.Corresponds`
and `Prosody.syntaxProsodyMax`, the deficiency of that relation between the constituents and the
π-nodes of a candidate. Where the constituents have distinct spans each containing its head,
MAX(α, π) is violated no more often than Match(α, π) (`Prosody.deficiency_corresponds_le`).

## References

* [ito-mester-2019]
-/

@[expose] public section

namespace Prosody

open OptimalityTheory

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
def syntaxProsodyMax {M : Type*} (α : List HeadedSpan) (π : Level) :
    Constraint (RoseTree (Constituent Level M)) :=
  fun t ↦ α.deficiency (Corresponds α) (levelSpans π t)

variable {α : List HeadedSpan}

/-- **Existential correspondence asks no more than Match** ([ito-mester-2019]): where the
constituents of `α` have distinct spans each containing its head, fewer of them lack a
corresponding node than lack a node of the same span. -/
theorem deficiency_corresponds_le (hα : (α.map (·.span)).Nodup)
    (hhead : ∀ a ∈ α, a.head ∈ Set.Ico a.span.fst a.span.snd) (m : List (NonemptyInterval ℕ)) :
    α.deficiency (Corresponds α) m ≤
      (Correspondence.ofRel (fun a p ↦ a.span = p) α.get m.get).maxViol :=
  Correspondence.deficiency_le_maxViol_ofRel (List.Nodup.of_map _ hα)
    (fun a ha _ hp ↦ hp ▸ ⟨hhead a ha, fun _ _ ↦ id⟩)
    fun _ ha _ ha' _ h h' ↦ List.inj_on_of_nodup_map hα ha ha' (h.trans h'.symm)

-- Two sister phrases share no corresponding φ when phrased together, and each has its own when
-- phrased apart. A φ over T serves only one of the two projections T heads, so the higher one
-- needs a φ of its own.
example : syntaxProsodyMax [⟨⟨(0, 1), by decide⟩, 0⟩, ⟨⟨(1, 2), by decide⟩, 1⟩] .ph
    (Tree.ph [.om [.σ], .om [.σ]]) = 2 := by
  decide
example : syntaxProsodyMax [⟨⟨(0, 1), by decide⟩, 0⟩, ⟨⟨(1, 2), by decide⟩, 1⟩] .ph
    (Tree.ph [.ph [.om [.σ]], .ph [.om [.σ]]]) = 0 := by
  decide
example : syntaxProsodyMax
    [⟨⟨(0, 2), by decide⟩, 1⟩, ⟨⟨(0, 1), by decide⟩, 0⟩, ⟨⟨(1, 2), by decide⟩, 1⟩] .ph
    (Tree.iota [.ph [.om [.σ]], .ph [.om [.σ]]]) = 1 := by
  decide

end Prosody
