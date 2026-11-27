/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Nat.Notation
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Minimalist.Feature.Basic

/-!
# Lexical items

The leaves of syntactic objects are drawn from `SO₀`, the lexical items and syntactic features. A
lexical item is a category with its selectional stack, its phonological form and its feature
bundle, and a token of it is the item with the index that tells its tokens apart. The objects
built over tokens are in `SyntacticObject/Token.lean`.

## Main definitions

* `Minimalist.LexicalItem`, `Minimalist.LexicalItem.Token`

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1)
-/

@[expose] public section

namespace Minimalist

/-- A lexical item is a category with its selectional stack, a phonological form, empty for a
silent item, and a feature bundle. -/
structure LexicalItem where
  /-- The category. -/
  cat : Cat
  /-- The selectional stack, consumed left to right. -/
  sel : List Cat
  /-- The phonological form, empty for a silent item. -/
  phonForm : String
  /-- The feature bundle the item has in the lexicon. -/
  features : FeatureBundle
  deriving Repr, DecidableEq

/-- The lexical item of a category and selectional stack, silent and without features unless the
optional arguments say otherwise. -/
def LexicalItem.of (cat : Cat) (sel : List Cat) (phonForm : String := "")
    (features : FeatureBundle := ⊥) : LexicalItem :=
  ⟨cat, sel, phonForm, features⟩

/-- A token of a lexical item. Syntactic objects are compared as values, so two occurrences of
one item, the two *the*s of a transitive clause, are different leaves only through their tokens;
the index tells apart the tokens of one item, and tokens of different items differ anyway. -/
structure LexicalItem.Token where
  /-- The lexical item. -/
  item : LexicalItem
  /-- The index among the tokens of `item`. -/
  id : ℕ
  deriving Repr, DecidableEq

end Minimalist
