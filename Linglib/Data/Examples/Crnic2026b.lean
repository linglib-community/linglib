module

public import Linglib.Data.Examples.Schema

/-!
# `Crnic2026b` — typed example data

Auto-generated from `Linglib/Data/Examples/Crnic2026b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Crnic2026b.Examples`.
-/

@[expose] public section

namespace Crnic2026b.Examples

def ex_1 : Datum :=
  { id := "crnic2026b_1"
    source := ⟨"crnic-2026b", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only Gal was at the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("positive inference", "Gal was at the party"), ("exhaustive inference", "No one distinct from Gal was at the party")] }

def ex_25 : Datum :=
  { id := "crnic2026b_25"
    source := ⟨"crnic-2026b", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gal isn't only a grad student."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("positive inference", "Gal is at least a grad student")] }

def ex_48 : Datum :=
  { id := "crnic2026b_48"
    source := ⟨"crnic-2026b", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not only Gal was at the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("positive presupposition", "Gal was at the party")] }

def ex_107 : Datum :=
  { id := "crnic2026b_107"
    source := ⟨"crnic-2026b", "(107)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone but Gal was at the party."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1, ex_25, ex_48, ex_107]

end Crnic2026b.Examples
