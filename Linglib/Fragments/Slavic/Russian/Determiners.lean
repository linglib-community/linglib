module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Syntax.Person.Basic

/-!
# Russian demonstrative determiners

Russian has no articles. Its demonstratives *ètot* 'this', for something close to hand, and *tot*
'that', for something further removed, stand before a noun as well as alone, and before a noun they
are its determiners.

## References

* [wade-2020]
-/

@[expose] public section

namespace Russian.Determiners

/-- *ètot* (этот) 'this' before a noun, for something close to hand ([wade-2020] §126). -/
def ètot : DemonstrativeDeterminer := { form := "ètot", deixis := Person.first.participantSets }

/-- *tot* (тот) 'that' before a noun, for something further removed ([wade-2020] §126). -/
def tot : DemonstrativeDeterminer := { form := "tot", deixis := Person.first.participantSetsᶜ }

/-- The demonstrative determiners, masculine singular. -/
def allDemonstratives : List DemonstrativeDeterminer := [ètot, tot]

end Russian.Determiners
