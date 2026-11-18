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
precision, like *pristine*, and *dirty* like *filthy*, and each negated form takes what that
reading leaves of the literal meaning it shares with its simple antonym. These are Krifka's four
regions with the precise readings as the stereotypical uses, so a negated absolute [has a range
of its own exactly when its simple antonym is read more strictly than it literally
means](##degrees_plateau_nonempty_iff).

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

variable {D : Type*} (U : Set D) (stereotype : Polarity → Set D)

/-- *Not dirty* and *not clean* have ranges apart from *clean* and *dirty* exactly when the
simple forms are read at a precision that leaves out part of their literal meaning (p. 28); on
the literal reading alone the negated forms have none. -/
theorem degrees_plateau_nonempty_iff :
    ((Krifka2007b.Region.plateauHigh.degrees stereotype U).Nonempty ↔
        ¬ U ⊆ stereotype .positive) ∧
      ((Krifka2007b.Region.plateauLow.degrees stereotype U).Nonempty ↔
        ¬ Uᶜ ⊆ stereotype .negative) :=
  ⟨Set.sdiff_nonempty, Set.sdiff_nonempty⟩

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
