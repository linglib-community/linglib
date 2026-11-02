module

public import Linglib.Data.Examples.Schema

/-!
# `Elliott2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Elliott2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Elliott2023.Examples`.
-/

@[expose] public section

namespace Elliott2023.Examples

def ex_7 : Datum :=
  { id := "elliott2023_7"
    source := ⟨"elliott-2023", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there's no bathroom in this house, or it's in a funny place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2")] }

def ex_10 : Datum :=
  { id := "elliott2023_10"
    source := ⟨"elliott-2023", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Gabe doesn't have a credit card with him, or he paid with it."
    glossedTokens := []
    context := "We're wondering how Gabe paid for dinner."
    judgment := .acceptable
    alternatives := []
    readings := [("true if Gabe paid with one credit card and not with another", .acceptable)]
    paperFeatures := [("section", "1.2")] }

def ex_11a : Datum :=
  { id := "elliott2023_11a"
    source := ⟨"elliott-2023", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Gabe doesn't have an umbrella, or he remembered to bring it."
    glossedTokens := []
    context := "It has been raining all day. We're wondering whether Gabe got wet on the way here."
    judgment := .acceptable
    alternatives := []
    readings := [("Gabe remembered to bring some umbrella of his", .acceptable)]
    paperFeatures := [("section", "1.2")] }

def ex_11b : Datum :=
  { id := "elliott2023_11b"
    source := ⟨"elliott-2023", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Gabe doesn't have an umbrella, or he forgot to bring it."
    glossedTokens := []
    context := "It has been raining all day. We're wondering whether Gabe got wet on the way here."
    judgment := .acceptable
    alternatives := []
    readings := [("Gabe forgot to bring every umbrella of his", .acceptable)]
    paperFeatures := [("section", "1.2")] }

def ex_12 : Datum :=
  { id := "elliott2023_12"
    source := ⟨"elliott-2023", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Neither is there no bathroom in this house, nor is it in a funny place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("false as soon as there is a bathroom in this house in a funny place", .acceptable)]
    paperFeatures := [("section", "1.2")] }

def ex_24 : Datum :=
  { id := "elliott2023_24"
    source := ⟨"elliott-2023", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Steven doesn't own no car — it's a ferrari."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3")] }

def all : List Datum := [ex_7, ex_10, ex_11a, ex_11b, ex_12, ex_24]

end Elliott2023.Examples
