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
For absolutes the paper proposes that competition among equivalent forms invites
a precision-level reasoning: *clean* is read at a high precision, opening a gap
the complex forms fill. On a two-threshold scale this is exactly the observed
profile — both negated weak forms come apart from their simple antonyms
(`relative_like`) yet the residues are mirror images (`residues_symmetric`),
whereas at a single threshold neither distinction exists
(`Degree.AntonymForm.contradictoryDenotation_synonymy`).

## References

* [alexandropoulou-gotzner-2024b]
* [alexandropoulou-gotzner-2024a]
* [horn-1989]
* [kennedy-2007]
-/

@[expose] public section

namespace AlexandropoulouGotzner2024b

open Degree AlexandropoulouGotzner2024a

/-! ### Precision-level gap -/

variable {D : Type*} [LinearOrder D] (tp : ThresholdPair D)

theorem residues_symmetric :
    AntonymForm.strengthenedDenotation tp .notNegative \
        AntonymForm.strengthenedDenotation tp .positive =
      AntonymForm.strengthenedDenotation tp .notPositive \
        AntonymForm.strengthenedDenotation tp .negative :=
  (AntonymForm.strengthenedDenotation_notNegative_diff_positive tp).trans
    (AntonymForm.strengthenedDenotation_notPositive_diff_negative tp).symm

theorem relative_like (h : tp.neg ≤ tp.pos) :
    (AntonymForm.strengthenedDenotation tp .notNegative \
        AntonymForm.strengthenedDenotation tp .positive).Nonempty ∧
      (AntonymForm.strengthenedDenotation tp .notPositive \
        AntonymForm.strengthenedDenotation tp .negative).Nonempty := by
  rw [← residues_symmetric, and_self, AntonymForm.strengthenedDenotation_notNegative_diff_positive]
  exact tp.gap_nonempty_iff.2 h

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
