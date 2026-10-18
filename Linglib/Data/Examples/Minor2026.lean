module

public import Linglib.Data.Examples.Schema

/-!
# `Minor2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Minor2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Minor2026.Examples`.
-/

@[expose] public section

namespace Minor2026.Examples

def ex_93a : Datum :=
  { id := "minor2026_93a"
    source := ⟨"minor-2026", "(93a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Miles wants to meet a policeman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("want > ∃", .acceptable), ("∃ > want", .acceptable)]
    paperFeatures := [] }

def ex_93b : Datum :=
  { id := "minor2026_93b"
    source := ⟨"minor-2026", "(93b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Miles wants to meet policemen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("want > ∃", .acceptable), ("∃ > want", .unacceptable)]
    paperFeatures := [] }

def ex_93c : Datum :=
  { id := "minor2026_93c"
    source := ⟨"minor-2026", "(93c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All (of) the boys want to meet policemen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("want > ∃", .acceptable), ("∃ > want", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_93a, ex_93b, ex_93c]

end Minor2026.Examples
