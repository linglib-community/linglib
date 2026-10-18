module

public import Linglib.Data.Examples.Schema

/-!
# `Minor2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Minor2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Minor2022.Examples`.
-/

@[expose] public section

namespace Minor2022.Examples

def ex_1a : Datum :=
  { id := "minor2022_1a"
    source := ⟨"minor-2022", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the girls were wearing hats."
    glossedTokens := []
    context := "Each girl was wearing a single hat, and no two girls were wearing the same hat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licensor", "pluralQ"), ("dependent", "bare")] }

def ex_2a : Datum :=
  { id := "minor2022_2a"
    source := ⟨"minor-2022", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each girl was wearing hats."
    glossedTokens := []
    context := "Each girl was wearing a single hat, and no two girls were wearing the same hat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("licensor", "singularQ"), ("dependent", "bare")] }

def ex_3 : Datum :=
  { id := "minor2022_3"
    source := ⟨"minor-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the girls were wearing several hats."
    glossedTokens := []
    context := "Each girl was wearing a single hat, and no two girls were wearing the same hat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("licensor", "pluralQ"), ("dependent", "cardinal")] }

def ex_4 : Datum :=
  { id := "minor2022_4"
    source := ⟨"minor-2022", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls were wearing several hats."
    glossedTokens := []
    context := "Each girl was wearing a single hat, and no two girls were wearing the same hat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licensor", "nonQ"), ("dependent", "cardinal")] }

def ex_11a : Datum :=
  { id := "minor2022_11a"
    source := ⟨"minor-2022", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls were all wearing hats."
    glossedTokens := []
    context := "Each girl was wearing a single hat, and no two girls were wearing the same hat."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licensor", "pluralQ"), ("dependent", "bare")] }

def ex_13 : Datum :=
  { id := "minor2022_13"
    source := ⟨"minor-2022", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls were each wearing hats."
    glossedTokens := []
    context := "Each girl was wearing a single hat, and no two girls were wearing the same hat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("licensor", "singularQ"), ("dependent", "bare")] }

def all : List Datum := [ex_1a, ex_2a, ex_3, ex_4, ex_11a, ex_13]

end Minor2022.Examples
