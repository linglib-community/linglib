module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Thai determiner inventory

Thai patterns with Mandarin, as Jenks reports for both: bare nouns serve
unique definites, the demonstrative *nán* 'that'
obligatorily expones anaphoric definites including donkey anaphora, and
possession is marked with *khɔ̌ɔng*.

## References

* [jenks-2015]
* [jenks-2018]
* [moroney-2021]
-/

@[expose] public section

namespace Thai.Determiners

/-- The Thai determiners are the demonstrative *nán*, the obligatory exponent
    of anaphoric definites including donkey anaphora, and the possessive
    *khɔ̌ɔng*. -/
def inventory : Determiner.Inventory :=
  [ .demonstrative
      { form := "nan", deixis := Person.first.participantSetsᶜ,
        uses := {.anaphoric} },
    .possessive { form := "khong" } ]

theorem strengths_inventory : inventory.strengths = {.familiarity} := by decide

end Thai.Determiners
