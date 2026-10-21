module

public import Mathlib.Order.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.DeriveFintype

/-!
# Bybee's relevance hierarchy

[bybee-1985] ranks the verbal inflectional categories by their relevance to the verb, the extent
to which the category's meaning directly affects the meaning of the stem: valence, voice,
aspect, tense, mood and agreement "are ranked for relevance to verbs in that order". A more
relevant category is predicted to have morphological expression, inflectional or derivational,
in more languages, to sit closer to the stem, and to fuse with it more tightly. The scale alone
does not predict which categories are most often inflectional: generality works against the most
relevant, so inflection is likeliest in the middle of the scale.

`RelevanceHierarchy` is a comparative concept, not a universal slot inventory: languages own the
slot types of their `AffixTemplate`s (`Mayan.VerbSlot`, `Japanese.Verb.Slot`), and a relevance claim
pulls the order back along a partial map from slots to categories supplied by the study that
draws the comparison. A slot sequence read stem-outward respects the hierarchy when it is
`List.SortedLE`.

## Main definitions

* `Morphology.RelevanceHierarchy`: Bybee's six categories, linearly ordered from the most
  relevant.

## Implementation notes

Bybee calls the order approximate, and her diagram of it lists number, person and gender
agreement as three rows at the bottom; the hierarchy takes her single category of agreement,
which is what her morpheme-order survey and later comparisons test. Categories outside her list,
such as derivation, negation or nonfiniteness, have no rank: a slot of that kind maps to nothing.

## References

* [J. Bybee, *Morphology: A Study of the Relation between Meaning and Form* (1985)][bybee-1985]
-/

@[expose] public section

namespace Morphology

/-- [bybee-1985]'s verbal inflectional categories in order of relevance to the verb, the most
relevant first. -/
inductive RelevanceHierarchy where
  /-- The number or role of the verb's arguments. -/
  | valence
  /-- The perspective from which the situation described by the verb is viewed. -/
  | voice
  /-- The internal temporal constituency of the situation. -/
  | aspect
  /-- The placement of the situation in time. -/
  | tense
  /-- How the speaker presents the truth of the proposition, evidentials included. -/
  | mood
  /-- Person, number and gender agreement with the verb's arguments. -/
  | agreement
  deriving DecidableEq, Repr, Fintype

namespace RelevanceHierarchy

/-- The categories are ordered as they are listed: `a < b` when `a` is the more relevant, and so
predicted to sit closer to the stem. -/
instance : LinearOrder RelevanceHierarchy :=
  LinearOrder.lift' RelevanceHierarchy.ctorIdx (by decide)

end RelevanceHierarchy

end Morphology
