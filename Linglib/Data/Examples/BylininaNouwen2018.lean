module

public import Linglib.Data.Examples.Schema

/-!
# `BylininaNouwen2018` — typed example data

Auto-generated from `Linglib/Data/Examples/BylininaNouwen2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BylininaNouwen2018.Examples`.
-/

@[expose] public section

namespace BylininaNouwen2018.Examples

def ex12 : Datum :=
  { id := "bylininanouwen2018_ex12"
    source := ⟨"bylinina-nouwen-2018", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student has visited me in years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "strong"), ("npi", "in years")] }

def ex13 : Datum :=
  { id := "bylininanouwen2018_ex13"
    source := ⟨"bylinina-nouwen-2018", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Zero students have visited me in years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "zero"), ("strength", "strong"), ("npi", "in years")] }

def ex14 : Datum :=
  { id := "bylininanouwen2018_ex14"
    source := ⟨"bylinina-nouwen-2018", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student ever said anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "weak"), ("npi", "ever"), ("npi", "anything")] }

def ex15 : Datum :=
  { id := "bylininanouwen2018_ex15"
    source := ⟨"gajewski-2011", "(112)"⟩
    reportedIn := some ⟨"bylinina-nouwen-2018", "(15)"⟩
    language := "stan1293"
    primaryText := "Zero students said anything."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "zero"), ("strength", "weak"), ("npi", "anything")] }

def ex16 : Datum :=
  { id := "bylininanouwen2018_ex16"
    source := ⟨"bylinina-nouwen-2018", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Zero students bought any car."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "zero"), ("strength", "weak"), ("npi", "any")] }

def ex46_no : Datum :=
  { id := "bylininanouwen2018_ex46_no"
    source := ⟨"bylinina-nouwen-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No students read any books by Auster."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "weak"), ("npi", "any")] }

def ex46_few : Datum :=
  { id := "bylininanouwen2018_ex46_few"
    source := ⟨"bylinina-nouwen-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few students read any books by Auster."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "few"), ("strength", "weak"), ("npi", "any")] }

def ex47_no : Datum :=
  { id := "bylininanouwen2018_ex47_no"
    source := ⟨"bylinina-nouwen-2018", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No students have visited me in years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "strong"), ("npi", "in years")] }

def ex47_few : Datum :=
  { id := "bylininanouwen2018_ex47_few"
    source := ⟨"bylinina-nouwen-2018", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few students have visited me in years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "few"), ("strength", "strong"), ("npi", "in years")] }

def all : List Datum := [ex12, ex13, ex14, ex15, ex16, ex46_no, ex46_few, ex47_no, ex47_few]

end BylininaNouwen2018.Examples
