module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Syntax.Person.Basic

/-!
# Spanish demonstrative determiners

The demonstrative determiners of Spanish locate the referent of their noun phrase near or in
association with the speaker (*este*), at any distance from the speaker (*ese*), and away from
both participants (*aquel*), which suggests distance and is rarely obligatory, since *ese* can
replace it wherever space rather than time is concerned. The articles are not recorded here.

## References

* [butt-benjamin-2019]
-/

@[expose] public section

namespace Spanish.Determiners

/-- *este* 'this', near to or associated with the speaker ([butt-benjamin-2019] §7.4.1). -/
def este : DemonstrativeDeterminer := { form := "este", deixis := Person.first.participantSets }

/-- *ese* 'that', at any distance from the speaker ([butt-benjamin-2019] §7.4.1). -/
def ese : DemonstrativeDeterminer := { form := "ese", deixis := Person.first.participantSetsᶜ }

/-- *aquel* 'that over there', not used for things close to the hearer or the speaker
([butt-benjamin-2019] §7.4.1). -/
def aquel : DemonstrativeDeterminer := { form := "aquel", deixis := Person.third.participantSets }

/-- The demonstrative determiners, masculine singular. -/
def allDemonstratives : List DemonstrativeDeterminer := [este, ese, aquel]

end Spanish.Determiners
