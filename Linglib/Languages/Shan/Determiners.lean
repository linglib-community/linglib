module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Shan determiner inventory

Shan (Southwestern Tai, Kra-Dai) has no articles. Its two main demonstratives, proximal *nâj*
'this' and distal *nân* 'that', follow the noun, directly or after a classifier. They are optional
where English uses the definite article anaphorically: a bare noun takes up an antecedent, the
product of a mentioned producer, or a donkey antecedent as well as a demonstrative phrase does. A
referent unique in the situation takes the bare noun alone. So no definite use calls for a
demonstrative, and the inventory marks neither strength of definite.

## TODO

* The quantifiers *ku* 'every' and *lǎajlǎaj* 'many', which take a classifier, and *nǎm* 'much,
  many', which does not.

## References

* [moroney-2021]
-/

@[expose] public section

namespace Shan.Determiners

/-- *nâj* 'this', the proximal demonstrative, locates its referent near the speaker. -/
def naj : DemonstrativeDeterminer := { form := "nâj", deixis := Person.first.participantSets }

/-- *nân* 'that', the distal demonstrative, locates its referent away from the speaker. -/
def nan : DemonstrativeDeterminer := { form := "nân", deixis := Person.first.participantSetsᶜ }

/-- The Shan determiners are the demonstratives, which no definite use requires. -/
def inventory : Determiner.Inventory := [.demonstrative naj, .demonstrative nan]

theorem strengths_inventory : inventory.strengths = ∅ := by decide

end Shan.Determiners
