module

public import Linglib.Data.Examples.Schema

/-!
# `AnandToosarvandani2019` — typed example data

Auto-generated from `Linglib/Data/Examples/AnandToosarvandani2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AnandToosarvandani2019.Examples`.
-/

@[expose] public section

namespace AnandToosarvandani2019.Examples

def ex_5 : Datum :=
  { id := "anandtoosarvandani2019_5"
    source := ⟨"anand-toosarvandani-2019", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The janitor turned off the lights. The room was empty now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("overlapping", .acceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "now")] }

def ex_7 : Datum :=
  { id := "anandtoosarvandani2019_7"
    source := ⟨"anand-toosarvandani-2019", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People began to leave. The room was empty now."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("overlapping", .unacceptable), ("forward-shifted", .unacceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "now"), ("aspect", "state cannot overlap")] }

def ex_8 : Datum :=
  { id := "anandtoosarvandani2019_8"
    source := ⟨"anand-toosarvandani-2019", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People began to leave. Now, the room was empty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forward-shifted", .acceptable)]
    paperFeatures := [("position", "initial"), ("demonstrative", "now"), ("sister", "yes"), ("anterior", "no")] }

def ex_29_initial : Datum :=
  { id := "anandtoosarvandani2019_29_initial"
    source := ⟨"anand-toosarvandani-2019", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How things have changed since the campaign! Cohen plead guilty last week and incurred Trump's wrath. Now, he enjoyed his full support."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("backshifted", .unacceptable)]
    paperFeatures := [("position", "initial"), ("demonstrative", "now"), ("sister", "yes"), ("anterior", "yes")] }

def ex_29_final : Datum :=
  { id := "anandtoosarvandani2019_29_final"
    source := ⟨"anand-toosarvandani-2019", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How things have changed since the campaign! Cohen plead guilty last week and incurred Trump's wrath. He enjoyed his full support now."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("backshifted", .unacceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "now"), ("anterior", "yes")] }

def ex_36a : Datum :=
  { id := "anandtoosarvandani2019_36a"
    source := ⟨"anand-toosarvandani-2019", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People began to leave. Then, the room was empty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forward-shifted", .acceptable)]
    paperFeatures := [("position", "initial"), ("demonstrative", "then"), ("sister", "yes"), ("anterior", "no")] }

def ex_36b : Datum :=
  { id := "anandtoosarvandani2019_36b"
    source := ⟨"anand-toosarvandani-2019", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People began to leave. The room was empty then."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("overlapping", .unacceptable), ("forward-shifted", .unacceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "then"), ("aspect", "state cannot overlap")] }

def ex_37 : Datum :=
  { id := "anandtoosarvandani2019_37"
    source := ⟨"anand-toosarvandani-2019", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How things have changed since the campaign! Cohen plead guilty last week and incurred Trump's wrath. Then, he enjoyed his full support."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("backshifted", .acceptable)]
    paperFeatures := [("position", "initial"), ("demonstrative", "then"), ("sister", "yes"), ("anterior", "yes")] }

def ex_38 : Datum :=
  { id := "anandtoosarvandani2019_38"
    source := ⟨"anand-toosarvandani-2019", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cohen incurred Trump's wrath yesterday. Then, he enjoyed his full support."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("backshifted", .unacceptable), ("forward-shifted", .acceptable)]
    paperFeatures := [("position", "initial"), ("demonstrative", "then"), ("sister", "yes"), ("anterior", "no")] }

def ex_40a : Datum :=
  { id := "anandtoosarvandani2019_40a"
    source := ⟨"anand-toosarvandani-2019", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The janitor turned off the lights. The room was empty now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("overlapping", .acceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "now")] }

def ex_40b : Datum :=
  { id := "anandtoosarvandani2019_40b"
    source := ⟨"anand-toosarvandani-2019", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The janitor turned off the lights. The room was empty then."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("overlapping", .acceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "then")] }

def ex_47a : Datum :=
  { id := "anandtoosarvandani2019_47a"
    source := ⟨"anand-toosarvandani-2019", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whenever he used to go to a restaurant, Max would avoid all kinds of seafood. Recently, he got over his fear. He had a nice meal last night. Now, he ordered the salmon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("overlapping", .acceptable)]
    paperFeatures := [("position", "initial"), ("demonstrative", "now"), ("sister", "no"), ("anterior", "no")] }

def ex_47b : Datum :=
  { id := "anandtoosarvandani2019_47b"
    source := ⟨"anand-toosarvandani-2019", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whenever he used to go to a restaurant, Max would avoid all kinds of seafood. Recently, he got over his fear. He had a nice meal last night. He ordered the salmon now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("overlapping", .acceptable)]
    paperFeatures := [("position", "final"), ("demonstrative", "now")] }

def all : List Datum := [ex_5, ex_7, ex_8, ex_29_initial, ex_29_final, ex_36a, ex_36b, ex_37, ex_38, ex_40a, ex_40b, ex_47a, ex_47b]

end AnandToosarvandani2019.Examples
