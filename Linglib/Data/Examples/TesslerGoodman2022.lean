module

public import Linglib.Data.Examples.Schema

/-!
# `TesslerGoodman2022` — typed example data

Auto-generated from `Linglib/Data/Examples/TesslerGoodman2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TesslerGoodman2022.Examples`.
-/

@[expose] public section

namespace TesslerGoodman2022.Examples

def tg2022_tall_basketball : Datum :=
  { id := "tg2022_tall_basketball"
    source := ⟨"tessler-goodman-2022", "§3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "tall basketball player"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjective", "tall"), ("polarity", "positive"), ("noun", "basketball player"), ("prior_expectation", "high"), ("inferred_class", "superordinate")] }

def tg2022_short_basketball : Datum :=
  { id := "tg2022_short_basketball"
    source := ⟨"tessler-goodman-2022", "§3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "short basketball player"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjective", "short"), ("polarity", "negative"), ("noun", "basketball player"), ("prior_expectation", "high"), ("inferred_class", "subordinate")] }

def tg2022_tall_jockey : Datum :=
  { id := "tg2022_tall_jockey"
    source := ⟨"tessler-goodman-2022", "§3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "tall jockey"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjective", "tall"), ("polarity", "positive"), ("noun", "jockey"), ("prior_expectation", "low"), ("inferred_class", "subordinate")] }

def tg2022_short_jockey : Datum :=
  { id := "tg2022_short_jockey"
    source := ⟨"tessler-goodman-2022", "§3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "short jockey"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjective", "short"), ("polarity", "negative"), ("noun", "jockey"), ("prior_expectation", "low"), ("inferred_class", "superordinate")] }

def all : List Datum := [tg2022_tall_basketball, tg2022_short_basketball, tg2022_tall_jockey, tg2022_short_jockey]

end TesslerGoodman2022.Examples
