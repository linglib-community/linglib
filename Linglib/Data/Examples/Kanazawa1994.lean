module

public import Linglib.Data.Examples.Schema

/-!
# `Kanazawa1994` — typed example data

Auto-generated from `Linglib/Data/Examples/Kanazawa1994.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kanazawa1994.Examples`.
-/

@[expose] public section

namespace Kanazawa1994.Examples

def strong_dominant : Datum :=
  { id := "kanazawa1994_strong_dominant"
    source := ⟨"kanazawa-1994", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey beats it."
    glossedTokens := []
    context := "Out of the blue"
    judgment := .acceptable
    contrasts := []
    readings := [("strong/universal", .acceptable), ("weak/existential", .acceptable)]
    paperFeatures := [("preferred_reading", "strong"), ("quantifier_monotonicity", "left downward")] }

def all : List Datum := [strong_dominant]

end Kanazawa1994.Examples
