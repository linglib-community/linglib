module

public import Linglib.Data.Examples.Schema

/-!
# `Jaeger2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Jaeger2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jaeger2014.Examples`.
-/

@[expose] public section

namespace Jaeger2014.Examples

def ex_1a : Datum :=
  { id := "jaeger2014_1a"
    source := ⟨"jaeger-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boys came in."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not all boys came in", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "Q"), ("implicature", "Not all boys came in."), ("signal", "f12"), ("world", "w2")] }

def ex_1b : Datum :=
  { id := "jaeger2014_1b"
    source := ⟨"jaeger-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three boys came in."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exactly three boys came in", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "Q"), ("implicature", "Exactly three boys came in.")] }

def ex_2a : Datum :=
  { id := "jaeger2014_2a"
    source := ⟨"jaeger-2014", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's book is good."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("the book that John is reading or that he has written is good", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "I")] }

def ex_2b : Datum :=
  { id := "jaeger2014_2b"
    source := ⟨"jaeger-2014", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a secretary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a female secretary", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "I")] }

def ex_2c : Datum :=
  { id := "jaeger2014_2c"
    source := ⟨"jaeger-2014", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "road"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("hard-surfaced road", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "I")] }

def ex_3a : Datum :=
  { id := "jaeger2014_3a"
    source := ⟨"jaeger-2014", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John stopped the car."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John stopped the car in a regular way, like using the foot brake", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "M"), ("signal", "f"), ("cost", "0"), ("world", "w1")] }

def ex_3b : Datum :=
  { id := "jaeger2014_3b"
    source := ⟨"jaeger-2014", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John made the car stop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John stopped the car in an abnormal way", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "M"), ("signal", "f'"), ("cost", "1"), ("world", "w2")] }

def ex_4 : Datum :=
  { id := "jaeger2014_4"
    source := ⟨"jaeger-2014", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John brought the car to a stop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John stopped the car in a non-stereotypical way", .acceptable)]
    paperFeatures := [("section", "5"), ("heuristic", "M")] }

def ex_5a : Datum :=
  { id := "jaeger2014_5a"
    source := ⟨"jaeger-2014", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The distance is 100 m."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("vague, between 90 and 110 meter", .acceptable), ("precise", .acceptable)]
    paperFeatures := [("section", "5"), ("principle", "RN/RI"), ("precision", "low")] }

def ex_5b : Datum :=
  { id := "jaeger2014_5b"
    source := ⟨"jaeger-2014", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The distance is 101 m."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("precise, with a slack of at most 50 cm", .acceptable)]
    paperFeatures := [("section", "5"), ("principle", "RN/RI"), ("precision", "high")] }

def ex_6 : Datum :=
  { id := "jaeger2014_6"
    source := ⟨"jaeger-2014", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The distance is exactly 100 m."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("precise", .acceptable)]
    paperFeatures := [("section", "5"), ("principle", "RN/RI"), ("precision", "high")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_2c, ex_3a, ex_3b, ex_4, ex_5a, ex_5b, ex_6]

end Jaeger2014.Examples
