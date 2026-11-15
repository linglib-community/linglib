module

public import Linglib.Data.Examples.Schema

/-!
# `Larson1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Larson1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Larson1998.Examples`.
-/

@[expose] public section

namespace Larson1998.Examples

def ex_1a : Datum :=
  { id := "larson1998_1a"
    source := ⟨"larson-1998", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Olga is a beautiful dancer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "beautiful")] }

def ex_2a : Datum :=
  { id := "larson1998_2a"
    source := ⟨"larson-1998", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kathrin is an intelligent student."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "intelligent")] }

def ex_2b : Datum :=
  { id := "larson1998_2b"
    source := ⟨"larson-1998", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "George is a skillful manager."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "skillful")] }

def ex_2c : Datum :=
  { id := "larson1998_2c"
    source := ⟨"larson-1998", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yo-yo is a good cellist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "good")] }

def ex_2d : Datum :=
  { id := "larson1998_2d"
    source := ⟨"larson-1998", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is a diligent president."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "diligent")] }

def ex_2e : Datum :=
  { id := "larson1998_2e"
    source := ⟨"larson-1998", "(2e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter is an old friend."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "old")] }

def ex_15 : Datum :=
  { id := "larson1998_15"
    source := ⟨"larson-1998", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jerry is an aged president."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .unacceptable)]
    paperFeatures := [("adjective", "aged")] }

def ex_16 : Datum :=
  { id := "larson1998_16"
    source := ⟨"larson-1998", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jerry is a former president."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .unacceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "former")] }

def ex_17a : Datum :=
  { id := "larson1998_17a"
    source := ⟨"larson-1998", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is a blonde and fast dancer."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "blonde"), ("adjective", "fast")] }

def ex_17b : Datum :=
  { id := "larson1998_17b"
    source := ⟨"larson-1998", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is a blonde and beautiful dancer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .acceptable), ("event", .unacceptable)]
    paperFeatures := [("adjective", "blonde"), ("adjective", "beautiful")] }

def ex_17c : Datum :=
  { id := "larson1998_17c"
    source := ⟨"larson-1998", "(17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is a fast and beautiful dancer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("individual", .unacceptable), ("event", .acceptable)]
    paperFeatures := [("adjective", "fast"), ("adjective", "beautiful")] }

def all : List Datum := [ex_1a, ex_2a, ex_2b, ex_2c, ex_2d, ex_2e, ex_15, ex_16, ex_17a, ex_17b, ex_17c]

end Larson1998.Examples
