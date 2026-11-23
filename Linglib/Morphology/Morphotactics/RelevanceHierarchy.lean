module

public import Linglib.Morphology.Morphotactics.Template.Scale
public import Mathlib.Order.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.DeriveFintype

/-!
# Bybee's relevance hierarchy

[bybee-1985] ranks the categories of verbal inflection by their relevance to the verb: valence,
voice, aspect, tense, mood and agreement, in that order. `RelevanceHierarchy` is that scale with
its linear order.

The scale is compared with a template through a partial map `cat` from the template's positions
to the scale, which a study supplies. The suffixes of the template respect the hierarchy when
`Morphotactics.Template.SuffixesAscend cat` holds, and its prefixes when
`Morphotactics.Template.PrefixesAscend cat` does.

## Implementation notes

The scale is a comparative concept and not an inventory of positions: a language's fragment owns
the positions of its templates. Bybee calls the order approximate, and her diagram lists number,
person and gender agreement as three rows; the scale takes her single category of agreement. A
category outside her list, such as derivation, negation or nonfiniteness, has no rank, and a
position of that kind maps to nothing.

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
