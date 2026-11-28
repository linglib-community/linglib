module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Haitian Creole determiner inventory

Haitian Creole (French-lexified, ISO `ht`) has a single post-nominal definite
determiner *la* (with phonologically conditioned variants) that covers
uniqueness at every level, anaphoric reference, both bridging types, and
covarying (donkey) uses, so it is one syncretic article rather than a
weak/strong split. Functional descriptions (*papa Mari* 'Mary's father')
surface without the article.

## References

* [schwarz-2013], §4.3
* [wespel-2008]
-/

@[expose] public section

namespace HaitianCreole.Determiners

/-- The definite *la* has the situational and the anaphoric uses and both kinds of bridging, as
from a book to *otè a* 'the author' and from a town to *meri a* 'the town hall'. -/
def la : Article :=
  { form := "la", definiteness := {.definite}, exponent := .dedicatedMorpheme,
    uses := {.immediateSituation, .largerSituation, .anaphoric, .bridging .partWhole,
      .bridging .relational} }

/-- The determiners are the single syncretic definite *la*. -/
def inventory : Determiner.Inventory := [.article la]

end HaitianCreole.Determiners
