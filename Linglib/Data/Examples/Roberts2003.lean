module

public import Linglib.Data.Examples.Schema

/-!
# `Roberts2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Roberts2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Roberts2003.Examples`.
-/

@[expose] public section

namespace Roberts2003.Examples

def enriched_definite : Datum :=
  { id := "roberts2003_enriched_definite"
    source := ⟨"roberts-2003", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A strange man lives here (and another one lives down the block). If the strange man who lives here sees a cat, he screams."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def two_strange_men : Datum :=
  { id := "roberts2003_two_strange_men"
    source := ⟨"roberts-2003", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A strange man lives here, and another one lives down the block. This situation makes me very nervous. If the strange man sees a cat, he screams. The other one never says anything at all."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [enriched_definite, two_strange_men]

end Roberts2003.Examples
