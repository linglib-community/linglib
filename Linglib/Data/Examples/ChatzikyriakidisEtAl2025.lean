module

public import Linglib.Data.Examples.Schema

/-!
# `ChatzikyriakidisEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/ChatzikyriakidisEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChatzikyriakidisEtAl2025.Examples`.
-/

@[expose] public section

namespace ChatzikyriakidisEtAl2025.Examples

def hobNob : Datum :=
  { id := "chatzikyriakidisetal2025_hobNob"
    source := ⟨"geach-1967", "the Hob-Nob sentence"⟩
    reportedIn := some ⟨"chatzikyriakidis-etal-2025", "§2.3.2"⟩
    language := "stan1293"
    primaryText := "Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the same witch) killed Cob's sow."
    glossedTokens := []
    context := "No witch need exist."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [hobNob]

end ChatzikyriakidisEtAl2025.Examples
