module

public import Linglib.Data.Examples.Schema

/-!
# `HeimKratzer1998` — typed example data

Auto-generated from `Linglib/Data/Examples/HeimKratzer1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HeimKratzer1998.Examples`.
-/

@[expose] public section

namespace HeimKratzer1998.Examples

def ch5_1 : Datum :=
  { id := "heimkratzer1998_ch5_1"
    source := ⟨"heim-kratzer-1998", "Ch. 5 (1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house which is empty is available."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("relative", "restrictive")] }

def ch5_2 : Datum :=
  { id := "heimkratzer1998_ch5_2"
    source := ⟨"heim-kratzer-1998", "Ch. 5 (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house, which is empty, is available."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("relative", "nonrestrictive")] }

def ch7_1a : Datum :=
  { id := "heimkratzer1998_ch7_1a"
    source := ⟨"heim-kratzer-1998", "Ch. 7 (1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every linguist offended John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("quantifier", "subject")] }

def ch7_1b : Datum :=
  { id := "heimkratzer1998_ch7_1b"
    source := ⟨"heim-kratzer-1998", "Ch. 7 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John offended every linguist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("quantifier", "object")] }

def ch7_2 : Datum :=
  { id := "heimkratzer1998_ch7_2"
    source := ⟨"heim-kratzer-1998", "Ch. 7 (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some publisher offended every linguist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("readings", "some > every; every > some")] }

def all : List Datum := [ch5_1, ch5_2, ch7_1a, ch7_1b, ch7_2]

end HeimKratzer1998.Examples
