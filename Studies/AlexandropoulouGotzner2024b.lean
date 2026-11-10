module

public import Studies.AlexandropoulouGotzner2024a
public import Linglib.Data.Examples.AlexandropoulouGotzner2024b
public import Linglib.Data.Examples.Readers

/-!
# Alexandropoulou and Gotzner (2024b): adjective interpretation and competition

Alexandropoulou and Gotzner re-run the rating experiments of their 2024a paper with one
statement per trial, removing the overt competition among the eight forms of an
item. The polarity asymmetry of weak relative antonyms persists and is larger
without competition, absolute antonyms stay symmetric in both modes, and negated
weak absolutes (*not dirty*, *not clean*) are nonetheless rated differently from
their truth-conditionally equivalent simple antonyms (*clean*, *dirty*).

The relative pattern is Horn's: R-strengthening of *not large* needs no
competitor, while the middling reading of *not small* rides on the semantic gap.
For absolutes the paper keeps the standard semantics, on which the pair leaves no gap, and
proposes a division of pragmatic labour at a level of precision: *clean* is read at a high
precision, like *pristine*, and *dirty* like *filthy*, so that [each negated form is used apart
from its simple antonym](##negated_apart), the two [on opposite sides of the
border](##dividedUse_subset), whereas [without the precise reading neither has a use of its
own](##AntonymForm.dividedUse_smul_self).

## References

* [alexandropoulou-gotzner-2024b]
* [alexandropoulou-gotzner-2024a]
* [horn-1989]
* [kennedy-2007]
-/

public section

namespace AlexandropoulouGotzner2024b

open AlexandropoulouGotzner2024a

/-! ### Division of labour at a level of precision -/

variable {D : Type*} (U : Set D) (core : Polarity → Set D)

/-- A negated absolute is used apart from the simple antonym it is truth-conditionally equivalent
to, *not dirty* from *clean* and *not clean* from *dirty* (p. 28). -/
theorem negated_apart (p : Polarity) :
    Disjoint (AntonymForm.dividedUse (· • U) core ⟨p, .negative⟩)
      (AntonymForm.dividedUse (· • U) core ⟨.negative * p, .positive⟩) :=
  AntonymForm.disjoint_dividedUse_flip ..

/-- *Not dirty* stays on the clean side of the border and *not clean* on the dirty side, so the
two negated forms communicate different ranges (p. 28). -/
theorem dividedUse_subset :
    AntonymForm.dividedUse (· • U) core .notNegative ⊆ U ∧
      AntonymForm.dividedUse (· • U) core .notPositive ⊆ Uᶜ :=
  ⟨fun _ h ↦ not_not.1 h.1, fun _ h ↦ h.1⟩

/-! ### Rows -/

theorem entails_iff_complementaryStandards :
    ∀ row ∈ Examples.all, row.feature? "modifier" = none →
      row.feature? "negation" = some "negated" →
      ∀ p ∈ (row.feature? "adjective").bind English.Adjectives.pairOf,
        (row.feature? "relation" = some "entails" ↔ p.ComplementaryStandards) := by
  decide

theorem readings_are_horn_ranges :
    ∀ row ∈ Examples.all, ∀ f ∈ formOf row, ∀ i ∈ row.feature? "inference",
      (i = "negative_strengthening" ↔ hornRanges f = {.negative}) ∧
      (i = "middling" ↔ hornRanges f = {.plateauLow, .plateauHigh}) := by
  decide

end AlexandropoulouGotzner2024b
