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

/-- The definite *la* refers back to an antecedent or bridges by a relation, as from a book to
*loter la* 'the author'; a part of an antecedent, as the town hall of a village, is a bare
noun. -/
def la : Article :=
  { form := "la", definiteness := {.definite}, exponent := .dedicatedMorpheme,
    uses := {.anaphoric, .bridging .relational} }

/-- The determiners are the single strong definite *la*. -/
def inventory : Determiner.Inventory := [.article la]

theorem strengths_inventory : inventory.strengths = {.familiarity} := by decide

end MauritianCreole.Determiners
