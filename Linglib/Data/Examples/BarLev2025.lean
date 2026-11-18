module

public import Linglib.Data.Examples.Schema

/-!
# `BarLev2025` — typed example data

Auto-generated from `Linglib/Data/Examples/BarLev2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarLev2025.Examples`.
-/

@[expose] public section

namespace BarLev2025.Examples

def ex_1a : Datum :=
  { id := "barlev2025_1a"
    source := ⟨"bar-lev-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four kids laughed."
    glossedTokens := []
    context := "Only half of the kids laughed."
    judgment := .acceptable
    contrasts := []
    readings := [("true in the context", .unacceptable)]
    paperFeatures := [("polarity", "positive"), ("predicate", "laugh")] }

def ex_1b : Datum :=
  { id := "barlev2025_1b"
    source := ⟨"bar-lev-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four kids didn't laugh."
    glossedTokens := []
    context := "Only half of the kids laughed."
    judgment := .acceptable
    contrasts := []
    readings := [("true in the context", .unacceptable)]
    paperFeatures := [("polarity", "negative"), ("predicate", "laugh")] }

def ex_2a : Datum :=
  { id := "barlev2025_2a"
    source := ⟨"bar-lev-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These four people weigh (exactly) 250 lbs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if the people together weigh exactly 250 lbs", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("predicate", "weigh 250 lbs"), ("homogeneity", "distributive")] }

def ex_2b : Datum :=
  { id := "barlev2025_2b"
    source := ⟨"bar-lev-2025", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These four people don't weigh (exactly) 250 lbs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if the people together do not weigh exactly 250 lbs", .acceptable), ("true if two of them together weigh 250 lbs and the other two each weigh less", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("predicate", "weigh 250 lbs"), ("homogeneity", "distributive")] }

def ex_3a : Datum :=
  { id := "barlev2025_3a"
    source := ⟨"bar-lev-2025", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four kids lifted the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if half of the kids lifted the table together and the other half did nothing", .unacceptable), ("true if half of the kids lifted the table together and the other half did too", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("predicate", "lift the table"), ("homogeneity", "total")] }

def ex_3b : Datum :=
  { id := "barlev2025_3b"
    source := ⟨"bar-lev-2025", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four kids didn't lift the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if half of the kids lifted the table together and the other half did nothing", .unacceptable)]
    paperFeatures := [("polarity", "negative"), ("predicate", "lift the table"), ("homogeneity", "total")] }

def ex_13_together : Datum :=
  { id := "barlev2025_13_together"
    source := ⟨"bar-lev-2025", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four kids didn't lift the table but they did together."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("predicate", "lift the table")] }

def ex_13_individually : Datum :=
  { id := "barlev2025_13_individually"
    source := ⟨"bar-lev-2025", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The four kids didn't lift the table but they did individually."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("predicate", "lift the table")] }

def ex_17_together : Datum :=
  { id := "barlev2025_17_together"
    source := ⟨"bar-lev-2025", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These two people don't weigh (exactly) 250 lbs but they do together."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("predicate", "weigh 250 lbs")] }

def ex_17_individually : Datum :=
  { id := "barlev2025_17_individually"
    source := ⟨"bar-lev-2025", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These two people don't weigh (exactly) 250 lbs but they do individually."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("predicate", "weigh 250 lbs")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_13_together, ex_13_individually, ex_17_together, ex_17_individually]

end BarLev2025.Examples
