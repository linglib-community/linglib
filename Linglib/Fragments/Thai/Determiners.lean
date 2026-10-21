module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Thai determiner inventory

Thai patterns with Mandarin ([jenks-2015]; [jenks-2018] reports identical
facts): bare nouns serve unique definites, the demonstrative *nán* 'that'
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
        uses := {.anaphoric, .donkey} },
    .possessive { form := "khong" } ]

/-- Thai derives the `.markedAnaphoric` Moroney cell. -/
theorem marking : inventory.markingStrategy = .markedAnaphoric := by decide

end Thai.Determiners
