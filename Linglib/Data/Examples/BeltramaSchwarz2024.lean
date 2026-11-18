module

public import Linglib.Data.Examples.Schema

/-!
# `BeltramaSchwarz2024` — typed example data

Auto-generated from `Linglib/Data/Examples/BeltramaSchwarz2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeltramaSchwarz2024.Examples`.
-/

@[expose] public section

namespace BeltramaSchwarz2024.Examples

def beltrama_schwarz_2024_1 : Datum :=
  { id := "beltrama_schwarz_2024_1"
    source := ⟨"beltrama-schwarz-2024", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 6 o'clock."
    glossedTokens := []
    context := "The time is 6:03."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def beltrama_schwarz_2024_2 : Datum :=
  { id := "beltrama_schwarz_2024_2"
    source := ⟨"beltrama-schwarz-2024", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ticket costs $200."
    glossedTokens := []
    context := "The price is $207."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [beltrama_schwarz_2024_1, beltrama_schwarz_2024_2]

end BeltramaSchwarz2024.Examples
