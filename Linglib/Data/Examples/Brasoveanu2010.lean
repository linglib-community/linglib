module

public import Linglib.Data.Examples.Schema

/-!
# `Brasoveanu2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Brasoveanu2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Brasoveanu2010.Examples`.
-/

@[expose] public section

namespace Brasoveanu2010.Examples

def ex_5 : Datum :=
  { id := "brasoveanu2010_5"
    source := ⟨"brasoveanu-2010", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Harvey courts a woman at every convention. She is very pretty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("same woman", .acceptable), ("possibly different women", .unacceptable)]
    paperFeatures := [] }

def ex_6 : Datum :=
  { id := "brasoveanu2010_6"
    source := ⟨"brasoveanu-2010", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Harvey courts a woman at every convention. She always comes to the banquet with him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("same woman", .acceptable), ("possibly different women", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_5, ex_6]

end Brasoveanu2010.Examples
