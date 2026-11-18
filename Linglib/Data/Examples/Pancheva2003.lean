module

public import Linglib.Data.Examples.Schema

/-!
# `Pancheva2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Pancheva2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pancheva2003.Examples`.
-/

@[expose] public section

namespace Pancheva2003.Examples

def ex1a_U : Datum :=
  { id := "pancheva2003_ex1a_U"
    source := ⟨"pancheva-2003", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 2000, Alexandra has lived in LA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "UNIVERSAL")] }

def ex1b_EXP : Datum :=
  { id := "pancheva2003_ex1b_EXP"
    source := ⟨"pancheva-2003", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has been in LA (before)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "EXPERIENTIAL")] }

def ex1c_RES : Datum :=
  { id := "pancheva2003_ex1c_RES"
    source := ⟨"pancheva-2003", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has (just) arrived in LA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "RESULTATIVE")] }

def ex5a_atelic : Datum :=
  { id := "pancheva2003_ex5a_atelic"
    source := ⟨"pancheva-2003", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have run."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "EXP")] }

def ex5b : Datum :=
  { id := "pancheva2003_ex5b"
    source := ⟨"pancheva-2003", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have built sandcastles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "EXP")] }

def ex6a_telic : Datum :=
  { id := "pancheva2003_ex6a_telic"
    source := ⟨"pancheva-2003", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have lost my glasses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "EXP or RES")] }

def ex6b : Datum :=
  { id := "pancheva2003_ex6b"
    source := ⟨"pancheva-2003", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have built a sandcastle."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "EXP or RES")] }

def ex13a : Datum :=
  { id := "pancheva2003_ex13a"
    source := ⟨"pancheva-2003", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been sick lately."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("reading", "EXP"), ("aspect", "NEUTRAL")] }

def ex16a : Datum :=
  { id := "pancheva2003_ex16a"
    source := ⟨"pancheva-2003", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been sick previously."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("reading", "EXP"), ("aspect", "BOUNDED")] }

def ex30c : Datum :=
  { id := "pancheva2003_ex30c"
    source := ⟨"pancheva-2003", "(30c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been drinking this cup of coffee right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("reading", "RES")] }

def all : List Datum := [ex1a_U, ex1b_EXP, ex1c_RES, ex5a_atelic, ex5b, ex6a_telic, ex6b, ex13a, ex16a, ex30c]

end Pancheva2003.Examples
