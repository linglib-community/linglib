module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Akan determiners

Akan (Kwa) has two determiners, both after the noun. The definite *nó* marks a familiar
referent, one mentioned before or present in the immediate situation, while a uniquely
identifiable referent is expressed by a bare noun. The indefinite *bí*, usually translated
'a certain', contrasts with a bare noun, which is also indefinite. Amfo describes *bí*, Arkoh and
Matthewson *nó*, and Owusu both; *nó* also occurs at the end of a clause, which is not recorded
here.

## Main definitions

* `Akan.Determiners.no`, `Akan.Determiners.bi`: the definite and the indefinite.
* `Akan.Determiners.inventory`: the determiners, which mark familiarity only
  (`strengths_inventory`).

## References

* [amfo-2010]
* [arkoh-matthewson-2013]
* [owusu-2022]
* [moroney-2021]
-/

@[expose] public section

namespace Akan.Determiners

/-- The definite *nó* marks a familiar referent. -/
def no : Article :=
  { form := "nó", definiteness := .definite, exponent := .dedicatedMorpheme,
    uses := {.anaphoric} }

/-- The indefinite *bí* is translated 'a certain'. -/
def bi : Article :=
  { form := "bí", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- The determiners. -/
def inventory : Determiner.Inventory := [.article no, .article bi]

/-- Only familiarity is marked. -/
theorem strengths_inventory : inventory.strengths = {.familiarity} := by decide

end Akan.Determiners
