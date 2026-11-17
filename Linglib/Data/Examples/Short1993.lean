module

public import Linglib.Data.Examples.Schema

/-!
# `Short1993` — typed example data

Auto-generated from `Linglib/Data/Examples/Short1993.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Short1993.Examples`.
-/

@[expose] public section

namespace Short1993.Examples

def musi : Datum :=
  { id := "short1993_musi"
    source := ⟨"short-1993-czech", "p. 510"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr se musí učit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def nemusi : Datum :=
  { id := "short1993_nemusi"
    source := ⟨"short-1993-czech", "p. 510"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr se nemusí učit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("affirmative", "short1993_musi")] }

def smi : Datum :=
  { id := "short1993_smi"
    source := ⟨"short-1993-czech", "p. 510"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr smí přijít."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def nesmi : Datum :=
  { id := "short1993_nesmi"
    source := ⟨"short-1993-czech", "p. 510"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr nesmí přijít."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("affirmative", "short1993_smi")] }

def all : List Datum := [musi, nemusi, smi, nesmi]

end Short1993.Examples
