module

public import Linglib.Data.Examples.Schema

/-!
# `Chierchia2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Chierchia2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chierchia2004.Examples`.
-/

@[expose] public section

namespace Chierchia2004.Examples

def ex128a : Datum :=
  { id := "chierchia2004_ex128a"
    source := ⟨"chierchia-2004", "(128a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that John ate the cake and drank any coffee"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "and")] }

def ex130a : Datum :=
  { id := "chierchia2004_ex130a"
    source := ⟨"chierchia-2004", "(130a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that John ate the cake or drank any coffee"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "or")] }

def all : List Datum := [ex128a, ex130a]

end Chierchia2004.Examples
