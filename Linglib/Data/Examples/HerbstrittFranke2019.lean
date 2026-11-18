module

public import Linglib.Data.Examples.Schema

/-!
# `HerbstrittFranke2019` — typed example data

Auto-generated from `Linglib/Data/Examples/HerbstrittFranke2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HerbstrittFranke2019.Examples`.
-/

@[expose] public section

namespace HerbstrittFranke2019.Examples

def ex1a : Datum :=
  { id := "herbstrittfranke2019_ex1a"
    source := ⟨"herbstritt-franke-2019", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The next ball drawn from this urn is probably red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("expression", "probably")] }

def ex1b : Datum :=
  { id := "herbstrittfranke2019_ex1b"
    source := ⟨"herbstritt-franke-2019", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not certain that the next ball drawn from this urn is red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("expression", "not certain")] }

def ex1c : Datum :=
  { id := "herbstrittfranke2019_ex1c"
    source := ⟨"herbstritt-franke-2019", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The next ball drawn from this urn is certainly red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("expression", "certainly")] }

def ex2 : Datum :=
  { id := "herbstrittfranke2019_ex2"
    source := ⟨"herbstritt-franke-2019", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Liem is definitely likely to be wearing green."
    glossedTokens := []
    context := "Eric has seen Liem wear green on 500 of 800 consecutive days."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("expression", "definitely likely")] }

def ex3 : Datum :=
  { id := "herbstrittfranke2019_ex3"
    source := ⟨"herbstritt-franke-2019", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It might be probable that Liem is wearing green."
    glossedTokens := []
    context := "Madeleine has seen Liem wear green on 5 of 8 consecutive days."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("expression", "might be probable")] }

def ex5a : Datum :=
  { id := "herbstrittfranke2019_ex5a"
    source := ⟨"herbstritt-franke-2019", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is probable that the next ball drawn from this urn will be red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("expression", "probable")] }

def ex6a : Datum :=
  { id := "herbstrittfranke2019_ex6a"
    source := ⟨"herbstritt-franke-2019", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is certainly probable that the next ball drawn from this urn will be red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("expression", "certainly probable")] }

def ex11 : Datum :=
  { id := "herbstrittfranke2019_ex11"
    source := ⟨"herbstritt-franke-2019", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The next ball will [...] be red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("expression", "frame")] }

def all : List Datum := [ex1a, ex1b, ex1c, ex2, ex3, ex5a, ex6a, ex11]

end HerbstrittFranke2019.Examples
