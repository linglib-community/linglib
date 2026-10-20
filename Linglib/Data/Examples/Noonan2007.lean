module

public import Linglib.Data.Examples.Schema

/-!
# `Noonan2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Noonan2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Noonan2007.Examples`.
-/

@[expose] public section

namespace Noonan2007.Examples

def ex_214b : Datum :=
  { id := "noonan2007_214b"
    source := ⟨"noonan-2007", "(214b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think that Floyd hit Roscoe"
    glossedTokens := []
    context := "Negated matrix, against (214a) I think that Floyd didn't hit Roscoe."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("verb", "think")] }

def ex_215b : Datum :=
  { id := "noonan2007_215b"
    source := ⟨"noonan-2007", "(215b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Zeke doesn't believe that Martians live in caves"
    glossedTokens := []
    context := "Negated matrix, against (215a) Zeke believes that Martians don't live in caves."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("verb", "believe")] }

def ex_216b : Datum :=
  { id := "noonan2007_216b"
    source := ⟨"noonan-2007", "(216b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hugh doesn't want Mary Ann to win"
    glossedTokens := []
    context := "Negated matrix, against (216a) Hugh wants Mary Ann not to win."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("verb", "want")] }

def ex_218 : Datum :=
  { id := "noonan2007_218"
    source := ⟨"noonan-2007", "(218)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't regret that Floyd hit Roscoe"
    glossedTokens := []
    context := "Negated matrix, against (217) I regret that Floyd didn't hit Roscoe."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .unacceptable)]
    paperFeatures := [("verb", "regret")] }

def all : List Datum := [ex_214b, ex_215b, ex_216b, ex_218]

end Noonan2007.Examples
