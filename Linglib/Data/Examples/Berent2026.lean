module

public import Linglib.Data.Examples.Schema

/-!
# `Berent2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Berent2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Berent2026.Examples`.
-/

@[expose] public section

namespace Berent2026.Examples

def dideb : Datum :=
  { id := "berent2026_dideb"
    source := ⟨"berent-2026", "p. 11"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "dideb"
    glossedTokens := []
    context := "A form on the root d-d-b, which begins with two identical consonants."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def bided : Datum :=
  { id := "berent2026_bided"
    source := ⟨"berent-2026", "p. 11"⟩
    reportedIn := none
    method := some .description
    language := "hebr1245"
    primaryText := "bided"
    glossedTokens := []
    context := "A form on the root b-d-d, which ends with two identical consonants."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [dideb, bided]

end Berent2026.Examples
