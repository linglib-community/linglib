module

public import Linglib.Data.Statistics.Schema

/-!
# KehlerRohde2019: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/KehlerRohde2019.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

A passage-completion experiment crossing the type of a relative clause on the direct object of an
object-biased implicit-causality verb (one inviting the inference of a cause of the matrix event or
not) with the prompt (a pronoun or nothing). The free-prompt continuations estimate the next-mention
prior and the production rates, the pronoun-prompt continuations the interpretation bias. Table 4
compares the observed rate of pronominal reference to the object with the rates predicted by the
Bayesian, Mirror and Expectancy models, and the fits of the three models over participant and item
means. The PDF read is the accepted manuscript, whose pagination differs from the journal's. The
rates are printed without the leading zero.

## References

* [kehler-rohde-2019]
-/

@[expose] public section

namespace KehlerRohde2019

open Data.Statistics

/-- The relative clause on the direct object of the context sentence. -/
inductive RC where
  /-- ExplRC: the relative clause invites the inference of a cause of the matrix event -/
  | explanation
  /-- NoExplRC: the relative clause invites no such inference -/
  | noExplanation
  deriving DecidableEq, Repr, Fintype

/-- The three models of the interpretation bias the paper compares. -/
inductive Model where
  /-- Bayesian: the next-mention prior reweighted by the production rate, equation (3) -/
  | bayesian
  /-- Mirror: the normalized production rate, equation (10) -/
  | mirror
  /-- Expectancy: the next-mention prior, equation (11) -/
  | expectancy
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 4: the observed and model-predicted rates at which a pronoun prompt is
interpreted as referring to the object, by relative clause. -/
structure ObjectReference where
  /-- The observed rate. -/
  actual : Decimal
  /-- The rate the Bayesian Model predicts. -/
  bayesian : Decimal
  /-- The rate the Mirror Model predicts. -/
  mirror : Decimal
  /-- The rate the Expectancy Model predicts. -/
  expectancy : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 4, by rc; from an experiment; checked against the page images. -/
def objectReference : RC → ObjectReference
  | .explanation => ⟨⟨215, 3⟩, ⟨229, 3⟩, ⟨321, 3⟩, ⟨385, 3⟩⟩
  | .noExplanation => ⟨⟨410, 3⟩, ⟨373, 3⟩, ⟨334, 3⟩, ⟨542, 3⟩⟩

/-- A row of Table 4: the R² of each model's predictions against the observed interpretation
biases, over participant and over item means. -/
structure Fit where
  /-- The R² over participant means. -/
  participants : Decimal
  /-- The R² over item means. -/
  items : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 4, by model; from an experiment; checked against the page images. -/
def fit : Model → Fit
  | .bayesian => ⟨⟨48, 2⟩, ⟨49, 2⟩⟩
  | .mirror => ⟨⟨34, 2⟩, ⟨42, 2⟩⟩
  | .expectancy => ⟨⟨14, 2⟩, ⟨12, 2⟩⟩

end KehlerRohde2019
