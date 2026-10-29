module

public import Linglib.Data.Examples.Schema

/-!
# `Spector2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Spector2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Spector2013.Examples`.
-/

@[expose] public section

namespace Spector2013.Examples

def ex30a : Datum :=
  { id := "spector2013_ex30a"
    source := ⟨"spector-2013", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the USA, one must be 18 years old in order to be allowed to vote."
    glossedTokens := []
    context := "The age requirement for voting in the USA is that voters be 18 years old or more."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("truthValue", "true")] }

def ex30b : Datum :=
  { id := "spector2013_ex30b"
    source := ⟨"spector-2013", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "One must be 40 years old in order to be eligible to the Fields medal."
    glossedTokens := []
    context := "There is a maximal age but no minimal age for being eligible to the Fields medal."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("truthValue", "false")] }

def ex36b : Datum :=
  { id := "spector2013_ex36b"
    source := ⟨"spector-2013", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have four chairs. In fact, I have five."
    glossedTokens := []
    context := "In answer to (36a): We need four chairs. Who could provide us with that?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2")] }

def ex39 : Datum :=
  { id := "spector2013_ex39"
    source := ⟨"spector-2013", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In order to be allowed to vote, one has to be 18 years old."
    glossedTokens := []
    context := "The minimal age required for voting is 18."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("truthValue", "true")] }

def ex40 : Datum :=
  { id := "spector2013_ex40"
    source := ⟨"spector-2013", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "One must be 6 feet tall in order to be hired in the military."
    glossedTokens := []
    context := "The minimal height for being hired in the military is 6 feet."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("truthValue", "true")] }

def all : List Datum := [ex30a, ex30b, ex36b, ex39, ex40]

end Spector2013.Examples
