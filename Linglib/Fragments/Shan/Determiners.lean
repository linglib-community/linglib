module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Shan determiner inventory

Shan (Southwestern Tai, Kra-Dai) has no overt definite or indefinite
articles, and its demonstratives *nâj/nân* are optional in anaphoric
contexts, so bare nouns express both unique and anaphoric definiteness.

## References

* [moroney-2021]
-/

@[expose] public section

namespace Shan.Determiners

/-- *nâj* 'this', the proximal demonstrative, which obligatorily expones no
    definite use. -/
def naj : DemonstrativeDeterminer := { form := "nâj", deixis := Person.first.participantSets }

/-- *nân* 'that', the distal demonstrative, which obligatorily expones no
    definite use. -/
def nan : DemonstrativeDeterminer := { form := "nân", deixis := Person.first.participantSetsᶜ }

/-- The Shan determiners are the optional demonstratives *nâj/nân*. -/
def inventory : Determiner.Inventory := [.demonstrative naj, .demonstrative nan]

/-- No strength is marked. -/
theorem strengths_inventory : inventory.strengths = ∅ := by decide

end Shan.Determiners
