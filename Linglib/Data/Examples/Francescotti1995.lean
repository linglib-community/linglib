module

public import Linglib.Data.Examples.Schema

/-!
# `Francescotti1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Francescotti1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Francescotti1995.Examples`.
-/

@[expose] public section

namespace Francescotti1995.Examples

def ex5 : Datum :=
  { id := "francescotti1995_ex5"
    source := ⟨"francescotti-1995", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Albert passed the exam."
    glossedTokens := []
    context := "Albert, one of the best chemistry students in the school's history, passed; Marie, the very best, was even more likely to pass."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("surpassed", "1"), ("neighbors", "3"), ("felicitous", "no")] }

def ex1 : Datum :=
  { id := "francescotti1995_ex1"
    source := ⟨"francescotti-1995", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Albert failed the exam."
    glossedTokens := []
    context := "Everyone in the class failed, Albert's failure being very surprising, and Marie's would be more so."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("surpassed", "2"), ("neighbors", "3"), ("felicitous", "yes")] }

def ex7 : Datum :=
  { id := "francescotti1995_ex7"
    source := ⟨"kay-1990", "lieutenant colonels"⟩
    reportedIn := some ⟨"francescotti-1995", "(7)"⟩
    language := "stan1293"
    primaryText := "The administration was so bewildered that they even had lieutenant colonels making policy decisions."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("surpassed", "2"), ("neighbors", "3"), ("felicitous", "yes")] }

def ex21far : Datum :=
  { id := "francescotti1995_ex21far"
    source := ⟨"francescotti-1995", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Andre cannot reach the top shelf."
    glossedTokens := []
    context := "Andre is by far the tallest person in the reference class."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("surpassed", "5"), ("neighbors", "5"), ("felicitous", "yes")] }

def ex21near : Datum :=
  { id := "francescotti1995_ex21near"
    source := ⟨"francescotti-1995", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Andre cannot reach the top shelf."
    glossedTokens := []
    context := "Andre is the tallest person in the reference class, but only by a small margin."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("surpassed", "5"), ("neighbors", "5"), ("felicitous", "yes")] }

def ex21half : Datum :=
  { id := "francescotti1995_ex21half"
    source := ⟨"francescotti-1995", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even Andre cannot reach the top shelf."
    glossedTokens := []
    context := "Half of the group is over six foot five, the other half under five foot, and Andre is barely in the taller half."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("surpassed", "2"), ("neighbors", "4"), ("felicitous", "no")] }

def all : List Datum := [ex5, ex1, ex7, ex21far, ex21near, ex21half]

end Francescotti1995.Examples
