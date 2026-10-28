module

public import Linglib.Data.Examples.Schema

/-!
# `Cohen2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Cohen2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cohen2013.Examples`.
-/

@[expose] public section

namespace Cohen2013.Examples

def ex_12b : Datum :=
  { id := "cohen2013_12b"
    source := ⟨"cohen-2013", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Storks have a favorite nesting area."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .acceptable)]
    paperFeatures := [("construction", "generic")] }

def ex_17a : Datum :=
  { id := "cohen2013_17a"
    source := ⟨"cohen-2013", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John smokes a cigarette."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("construction", "habitual")] }

def ex_17b : Datum :=
  { id := "cohen2013_17b"
    source := ⟨"cohen-2013", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John smokes a brand of French cigarette."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("construction", "habitual")] }

def ex_25a : Datum :=
  { id := "cohen2013_25a"
    source := ⟨"cohen-2013", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needed but didn't buy a new coat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("construction", "verb conjunction")] }

def all : List Datum := [ex_12b, ex_17a, ex_17b, ex_25a]

end Cohen2013.Examples
