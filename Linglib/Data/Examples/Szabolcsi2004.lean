module

public import Linglib.Data.Examples.Schema

/-!
# `Szabolcsi2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Szabolcsi2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Szabolcsi2004.Examples`.
-/

@[expose] public section

namespace Szabolcsi2004.Examples

def ex_10 : Datum :=
  { id := "szabolcsi2004_10"
    source := ⟨"szabolcsi-2004", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't call someone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not > some", .ungrammatical)]
    paperFeatures := [("item", "someone"), ("operator", "not")] }

def ex_11 : Datum :=
  { id := "szabolcsi2004_11"
    source := ⟨"szabolcsi-2004", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No one called someone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("no one > some", .ungrammatical)]
    paperFeatures := [("item", "someone"), ("operator", "no one")] }

def ex_12 : Datum :=
  { id := "szabolcsi2004_12"
    source := ⟨"szabolcsi-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John came to the party without someone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("without > some", .ungrammatical)]
    paperFeatures := [("item", "someone"), ("operator", "without")] }

def ex_13 : Datum :=
  { id := "szabolcsi2004_13"
    source := ⟨"szabolcsi-2004", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most five boys called someone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("at most 5 > some", .acceptable)]
    paperFeatures := [("item", "someone"), ("operator", "at most five")] }

def all : List Datum := [ex_10, ex_11, ex_12, ex_13]

end Szabolcsi2004.Examples
