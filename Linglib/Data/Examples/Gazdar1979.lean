module

public import Linglib.Data.Examples.Schema

/-!
# `Gazdar1979` — typed example data

Auto-generated from `Linglib/Data/Examples/Gazdar1979.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gazdar1979.Examples`.
-/

@[expose] public section

namespace Gazdar1979.Examples

def ex_18 : Datum :=
  { id := "gazdar1979_18"
    source := ⟨"gazdar-1979", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did it or Mary did it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not both", .acceptable)]
    paperFeatures := [] }

def ex_19 : Datum :=
  { id := "gazdar1979_19"
    source := ⟨"gazdar-1979", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did it or Mary did it or both of them did it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not both", .unacceptable)]
    paperFeatures := [] }

def ex_21 : Datum :=
  { id := "gazdar1979_21"
    source := ⟨"gazdar-1979", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the students were there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not all", .acceptable)]
    paperFeatures := [] }

def ex_22 : Datum :=
  { id := "gazdar1979_22"
    source := ⟨"gazdar-1979", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some, if not all, of the students were there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not all", .unacceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_18, ex_19, ex_21, ex_22]

end Gazdar1979.Examples
