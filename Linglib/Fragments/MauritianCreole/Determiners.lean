module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Mauritian Creole determiner inventory

Mauritian Creole (French-lexified, ISO `mfe`) has a single post-nominal
definite marker *la*, restricted to anaphoric reference and available in
covarying (donkey) uses; uniqueness definites are bare nominals.

## References

* [schwarz-2013], §4.1.2
* [wespel-2008]
-/

@[expose] public section

namespace MauritianCreole.Determiners

/-- The Mauritian Creole determiner inventory is the single strong definite
    *la*. -/
def inventory : Determiner.Inventory :=
  [ .article { form := "la", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.anaphoric} } ]

theorem strengths_inventory : inventory.strengths = {.familiarity} := by decide

end MauritianCreole.Determiners
