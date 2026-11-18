module

public import Linglib.Data.Examples.Schema

/-!
# `AlexiadouLohndal2017` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexiadouLohndal2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexiadouLohndal2017.Examples`.
-/

@[expose] public section

namespace AlexiadouLohndal2017.Examples

def ex_8a : Datum :=
  { id := "alexiadoulohndal2017_8a"
    source := ⟨"alexiadou-lohndal-2017", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the student of chemistry and the one of physics."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("stranded", "argument")] }

def ex_8b : Datum :=
  { id := "alexiadoulohndal2017_8b"
    source := ⟨"alexiadou-lohndal-2017", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the student with long hair and the one with short hair"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("stranded", "adjunct")] }

def ex_56a : Datum :=
  { id := "alexiadoulohndal2017_56a"
    source := ⟨"alexiadou-lohndal-2017", "(56a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "colored dark"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "color"), ("rootClass", "manner")] }

def ex_56b : Datum :=
  { id := "alexiadoulohndal2017_56b"
    source := ⟨"alexiadou-lohndal-2017", "(56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "blackened dark"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("root", "black"), ("rootClass", "result")] }

def all : List Datum := [ex_8a, ex_8b, ex_56a, ex_56b]

end AlexiadouLohndal2017.Examples
