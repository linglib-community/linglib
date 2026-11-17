module

public import Linglib.Data.Examples.Schema

/-!
# `KrizChemla2015` — typed example data

Auto-generated from `Linglib/Data/Examples/KrizChemla2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KrizChemla2015.Examples`.
-/

@[expose] public section

namespace KrizChemla2015.Examples

def ex_41a : Datum :=
  { id := "krizchemla2015_41a"
    source := ⟨"kriz-chemla-2015", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles are green."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-∅")] }

def ex_41b : Datum :=
  { id := "krizchemla2015_41b"
    source := ⟨"kriz-chemla-2015", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles are not green."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-∅")] }

def ex_14a : Datum :=
  { id := "krizchemla2015_14a"
    source := ⟨"kriz-chemla-2015", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In all the cells, the symbols are green."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-all")] }

def ex_15 : Datum :=
  { id := "krizchemla2015_15"
    source := ⟨"kriz-chemla-2015", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In none of the cells, the symbols are green."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-no")] }

def ex_16b : Datum :=
  { id := "krizchemla2015_16b"
    source := ⟨"kriz-chemla-2015", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In none of the cells are all the symbols green."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-no")] }

def ex_19 : Datum :=
  { id := "krizchemla2015_19"
    source := ⟨"kriz-chemla-2015", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy found his presents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-all")] }

def ex_20 : Datum :=
  { id := "krizchemla2015_20"
    source := ⟨"kriz-chemla-2015", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-no")] }

def ex_23 : Datum :=
  { id := "krizchemla2015_23"
    source := ⟨"kriz-chemla-2015", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the boys found their presents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-all")] }

def ex_24 : Datum :=
  { id := "krizchemla2015_24"
    source := ⟨"kriz-chemla-2015", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("embedding", "E-exactly")] }

def all : List Datum := [ex_41a, ex_41b, ex_14a, ex_15, ex_16b, ex_19, ex_20, ex_23, ex_24]

end KrizChemla2015.Examples
