/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TwoTier
public import Linglib.Phonology.Tone.Basic

/-!
# Jardine (2017): The local nature of tone-association patterns

This file formalizes Jardine's claim that tone-association patterns are local: each is
specified by a finite grammar `¬r₁ ∧ … ∧ ¬rₙ` of forbidden connected subgraphs of
autosegmental representations, so that well-formedness is checked, and learned, by scanning a
bounded window. The directional patterns of the paper's typology are the test case: Mende
allows plateaus and contours only at the right word edge, (4)–(5), and Hausa only at the left,
(6)–(7). The grammars (21) and (22) forbid non-final spreading and contours, and non-initial
ones, mirror images differing only in the edge. `Mende.free` and `Hausa.free` show every word
of (4) and (6) well formed under its own grammar, and `Mende.not_free_hántúnàa` and
`Hausa.not_free_félàmà` that each language's diagnostic form fails the other's grammar,
left-edge spreading being exactly what (21) forbids and right-edge spreading exactly what (22)
forbids, (18) and (16). Northern Karanga Shona, Kukuya, and Hirosaki Japanese, (23)–(38),
follow the same schema and are not formalized.

## Implementation notes

* Forbidden subgraphs are factors (`AR.FactorEmbeds`). The contour subgraph (19) leaves its
  two tones unordered so as to match rising as well as falling contours; a factor's tier word
  is ordered, so (19) is rendered as the pair of orders.

## References

* [jardine-2017]
-/

@[expose] public section

namespace Jardine2017

open Autosegmental Tone Tone.TRN

/-- The syllable, the paper's tone-bearing unit. -/
abbrev σ : TBUKind := .syllable

/-- A representation drawn as the paper does: a melody over a syllable string, with the
association lines given as pairs of positions. -/
abbrev ar (tones : List TRN) (tbus : List TBUKind) (lines : List (ℕ × ℕ)) :=
  AR.ofWords tones tbus fun p q => (p, q) ∈ lines

/-- The grammar of forbidden subgraphs `¬r₁ ∧ … ∧ ¬rₙ` of (3a), as the list of factors. -/
abbrev Grammar := List (AR (TwoTier TRN TBUKind))

/-! ### Mende: multiple association at the right edge -/

namespace Mende

/-- The words of (4), drawn as in (5): `mbû` 'owl', `ngílà` 'dog', `félàmà` 'junction',
`mbâ` 'companion', `nyàhâ` 'woman', `nìkílì` 'groundnut' — melody, syllables, lines. -/
def forms : List (List TRN × List TBUKind × List (ℕ × ℕ)) :=
  [([H, L], [σ], [(0, 0), (1, 0)]),
   ([H, L], [σ, σ], [(0, 0), (1, 1)]),
   ([H, L], [σ, σ, σ], [(0, 0), (1, 1), (1, 2)]),
   ([L, H, L], [σ], [(0, 0), (1, 0), (2, 0)]),
   ([L, H, L], [σ, σ], [(0, 0), (1, 1), (2, 1)]),
   ([L, H, L], [σ, σ, σ], [(0, 0), (1, 1), (2, 2)])]

/-- (17): a non-final H, and a non-final L, associated to two syllables. -/
abbrev nonfinalH := ar [H, L] [σ, σ] [(0, 0), (0, 1)]
abbrev nonfinalL := ar [L, H] [σ, σ] [(0, 0), (0, 1)]

/-- (19): a contour on a non-final syllable, in both tone orders. -/
abbrev nonfinalHL := ar [H, L] [σ, σ] [(0, 0), (1, 0)]
abbrev nonfinalLH := ar [L, H] [σ, σ] [(0, 0), (1, 0)]

/-- The Mende grammar (21). -/
def grammar : Grammar :=
  [nonfinalH, nonfinalL, nonfinalHL, nonfinalLH]

theorem free_grammar_iff (X : AR (TwoTier TRN TBUKind)) :
    X.Free grammar ↔ ¬ nonfinalH.FactorEmbeds X ∧ ¬ nonfinalL.FactorEmbeds X ∧
      ¬ nonfinalHL.FactorEmbeds X ∧ ¬ nonfinalLH.FactorEmbeds X := by
  simp only [grammar, AR.free_cons, AR.free_nil, and_true]

instance (tones : List TRN) (tbus : List TBUKind) (lines : List (ℕ × ℕ)) :
    Decidable ((ar tones tbus lines).Free grammar) :=
  decidable_of_iff _ (free_grammar_iff _).symm

/-- Every word of (4) is well-formed under (21). -/
theorem free : ∀ f ∈ forms, (ar f.1 f.2.1 f.2.2).Free grammar := by decide

end Mende

/-! ### Hausa: multiple association at the left edge -/

namespace Hausa

/-- The words of (6), drawn as in (7): `fáadì` 'fall', `hántúnàa` 'noses', `búhúnhúnàa`
'sacks', `mántá` 'forget', `káràntá` 'read', `kákkáràntá` 'reread' — melody, syllables,
lines. -/
def forms : List (List TRN × List TBUKind × List (ℕ × ℕ)) :=
  [([H, L], [σ, σ], [(0, 0), (1, 1)]),
   ([H, L], [σ, σ, σ], [(0, 0), (0, 1), (1, 2)]),
   ([H, L], [σ, σ, σ, σ], [(0, 0), (0, 1), (0, 2), (1, 3)]),
   ([H, L, H], [σ, σ], [(0, 0), (1, 0), (2, 1)]),
   ([H, L, H], [σ, σ, σ], [(0, 0), (1, 1), (2, 2)]),
   ([H, L, H], [σ, σ, σ, σ], [(0, 0), (0, 1), (1, 2), (2, 3)])]

/-- (22): a non-initial H, and a non-initial L, associated to two syllables. -/
abbrev noninitialH := ar [L, H] [σ, σ] [(1, 0), (1, 1)]
abbrev noninitialL := ar [H, L] [σ, σ] [(1, 0), (1, 1)]

/-- (22): a contour on a non-initial syllable, in both tone orders. -/
abbrev noninitialHL := ar [H, L] [σ, σ] [(0, 1), (1, 1)]
abbrev noninitialLH := ar [L, H] [σ, σ] [(0, 1), (1, 1)]

/-- The Hausa grammar (22). -/
def grammar : Grammar :=
  [noninitialH, noninitialL, noninitialHL, noninitialLH]

theorem free_grammar_iff (X : AR (TwoTier TRN TBUKind)) :
    X.Free grammar ↔ ¬ noninitialH.FactorEmbeds X ∧ ¬ noninitialL.FactorEmbeds X ∧
      ¬ noninitialHL.FactorEmbeds X ∧ ¬ noninitialLH.FactorEmbeds X := by
  simp only [grammar, AR.free_cons, AR.free_nil, and_true]

instance (tones : List TRN) (tbus : List TBUKind) (lines : List (ℕ × ℕ)) :
    Decidable ((ar tones tbus lines).Free grammar) :=
  decidable_of_iff _ (free_grammar_iff _).symm

/-- Every word of (6) is well-formed under (22). -/
theorem free : ∀ f ∈ forms, (ar f.1 f.2.1 f.2.2).Free grammar := by decide

end Hausa

/-! ### The contrast: the same subgraphs at opposite edges -/

/-- Hausa's `hántúnàa` (HHL, H spread at the left edge) contains (21)'s non-final H spread
((18a) is a valid Hausa representation). -/
theorem Mende.not_free_hántúnàa :
    ¬ (ar [H, L] [σ, σ, σ] [(0, 0), (0, 1), (1, 2)]).Free Mende.grammar := by decide

/-- Mende's `félàmà` (HLL, L spread at the right edge) contains (22)'s non-initial L
spread ((16a) is ill-formed in Hausa). -/
theorem Hausa.not_free_félàmà :
    ¬ (ar [H, L] [σ, σ, σ] [(0, 0), (1, 1), (1, 2)]).Free Hausa.grammar := by decide

end Jardine2017
