module

public import Linglib.Data.Examples.Schema

/-!
# `RosaArnold2017` — typed example data

Auto-generated from `Linglib/Data/Examples/RosaArnold2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RosaArnold2017.Examples`.
-/

@[expose] public section

namespace RosaArnold2017.Examples

def ex_1a : Datum :=
  { id := "rosaarnold2017_1a"
    source := ⟨"rosa-arnold-2017", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler blamed the chauffeur because he..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("murdered someone", .acceptable)]
    paperFeatures := [("verbType", "implicitCausality"), ("expected", "stimulus")] }

def ex_1b : Datum :=
  { id := "rosaarnold2017_1b"
    source := ⟨"rosa-arnold-2017", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler impressed the chauffeur because he..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("figured out the case", .acceptable)]
    paperFeatures := [("verbType", "implicitCausality"), ("expected", "stimulus")] }

def ex_2a : Datum :=
  { id := "rosaarnold2017_2a"
    source := ⟨"rosa-arnold-2017", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler gave the threatening note to the chauffeur and he..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("turned it in to the police", .acceptable)]
    paperFeatures := [("verbType", "transfer"), ("expected", "goal")] }

def ex_2b : Datum :=
  { id := "rosaarnold2017_2b"
    source := ⟨"rosa-arnold-2017", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler received a ticking bomb from the chauffeur and he..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("chucked it into the river", .acceptable)]
    paperFeatures := [("verbType", "transfer"), ("expected", "goal")] }

def ex_3a : Datum :=
  { id := "rosaarnold2017_3a"
    source := ⟨"rosa-arnold-2017", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sir Barnes got a backrub from Lady Mannerly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("role", "goal"), ("gram", "subject")] }

def ex_3b : Datum :=
  { id := "rosaarnold2017_3b"
    source := ⟨"rosa-arnold-2017", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lady Mannerly gave a backrub to Sir Barnes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("role", "goal"), ("gram", "nonsubject")] }

def ex_4a : Datum :=
  { id := "rosaarnold2017_4a"
    source := ⟨"rosa-arnold-2017", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The chef handed a cookbook to the maid."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("role", "source"), ("gram", "subject")] }

def ex_4b : Datum :=
  { id := "rosaarnold2017_4b"
    source := ⟨"rosa-arnold-2017", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The maid took a cookbook from the chef."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("role", "source"), ("gram", "nonsubject")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b]

end RosaArnold2017.Examples
