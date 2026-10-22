module

public import Linglib.Data.Examples.Schema

/-!
# `Ke2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Ke2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ke2026.Examples`.
-/

@[expose] public section

namespace Ke2026.Examples

def ex13 : Datum :=
  { id := "ke2026_ex13"
    source := ⟨"ke-2026", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To whom will he say that Mary gave the book?"
    glossedTokens := []
    context := "Successive-cyclic wh-movement through the edges of vP1, CP1, vP2 and CP2."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "successiveCyclic")] }

def all : List Datum := [ex13]

end Ke2026.Examples
