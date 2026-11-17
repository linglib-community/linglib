module

public import Linglib.Data.Examples.Schema

/-!
# `GuerriniWehbe2025` — typed example data

Auto-generated from `Linglib/Data/Examples/GuerriniWehbe2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GuerriniWehbe2025.Examples`.
-/

@[expose] public section

namespace GuerriniWehbe2025.Examples

def ex_9a : Datum :=
  { id := "guerriniwehbe2025_9a"
    source := ⟨"guerrini-wehbe-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that all of John's kids are adopted but today I discovered something amazing. All 10 of John's kids are adopted!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("presupposition", "John has 10 kids")] }

def ex_9b : Datum :=
  { id := "guerriniwehbe2025_9b"
    source := ⟨"guerrini-wehbe-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that all of John's kids are adopted but today I discovered something amazing. John has 10 adopted kids!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10a : Datum :=
  { id := "guerriniwehbe2025_10a"
    source := ⟨"guerrini-wehbe-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary read at least some of the books, but today I learned something interesting. She read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive")] }

def ex_10b : Datum :=
  { id := "guerriniwehbe2025_10b"
    source := ⟨"guerrini-wehbe-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Mary didn't read all of the books, but today I learned something interesting. She didn't read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative")] }

def ex_12a : Datum :=
  { id := "guerriniwehbe2025_12a"
    source := ⟨"guerrini-wehbe-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't married to any of his teammates."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "quantifier")] }

def ex_12b : Datum :=
  { id := "guerriniwehbe2025_12b"
    source := ⟨"guerrini-wehbe-2025", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't married to his teammates."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "definite plural")] }

def ex_13a : Datum :=
  { id := "guerriniwehbe2025_13a"
    source := ⟨"guerrini-wehbe-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the candidates won."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "quantifier")] }

def ex_13b : Datum :=
  { id := "guerriniwehbe2025_13b"
    source := ⟨"guerrini-wehbe-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the candidates lost."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("nominal", "quantifier")] }

def ex_13c : Datum :=
  { id := "guerriniwehbe2025_13c"
    source := ⟨"guerrini-wehbe-2025", "(13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates didn't win."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("nominal", "definite plural")] }

def ex_13d : Datum :=
  { id := "guerriniwehbe2025_13d"
    source := ⟨"guerrini-wehbe-2025", "(13d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates lost."
    glossedTokens := []
    context := "The rules for this year's election are that the person with the most votes wins, but if there is a tie for most votes, all of the candidates lose. This year.."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("nominal", "definite plural")] }

def ex_23 : Datum :=
  { id := "guerriniwehbe2025_23"
    source := ⟨"guerrini-wehbe-2025", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that not all of the students smiled, but today I learned something interesting. The students didn't smile."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_10b, ex_12a, ex_12b, ex_13a, ex_13b, ex_13c, ex_13d, ex_23]

end GuerriniWehbe2025.Examples
