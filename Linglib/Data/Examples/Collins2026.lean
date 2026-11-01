module

public import Linglib.Data.Examples.Schema

/-!
# `Collins2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Collins2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Collins2026.Examples`.
-/

@[expose] public section

namespace Collins2026.Examples

def ex_11 : Datum :=
  { id := "collins2026_11"
    source := ⟨"collins-2026", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John loves pictures of himself."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "collins2026_12a"
    source := ⟨"collins-2026", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pictures of himself, John loves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "collins2026_12b"
    source := ⟨"collins-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only pictures of himself does John love."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12c : Datum :=
  { id := "collins2026_12c"
    source := ⟨"collins-2026", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is pictures of himself that John loves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12d : Datum :=
  { id := "collins2026_12d"
    source := ⟨"collins-2026", "(12d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which pictures of himself does John love?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12e : Datum :=
  { id := "collins2026_12e"
    source := ⟨"collins-2026", "(12e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the pictures of himself that John loves"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_15 : Datum :=
  { id := "collins2026_15"
    source := ⟨"collins-2026", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every player didn't score."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not > every", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_11, ex_12a, ex_12b, ex_12c, ex_12d, ex_12e, ex_15]

end Collins2026.Examples
