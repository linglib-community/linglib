module

public import Linglib.Data.Examples.Schema

/-!
# `Chomsky2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Chomsky2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chomsky2015.Examples`.
-/

@[expose] public section

namespace Chomsky2015.Examples

def ex1 : Datum :=
  { id := "chomsky2015_ex1"
    source := ⟨"chomsky-2015", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which dog do you wonder John likes?"
    glossedTokens := []
    context := "The wh-phrase raised out of its criterial position, the specifier of the interrogative C."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("structure", "criterialRaised")] }

def ex2 : Datum :=
  { id := "chomsky2015_ex2"
    source := ⟨"chomsky-2015", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom read a book."
    glossedTokens := []
    context := "The subject raised from the specifier of v*P to the specifier of T."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "subject")] }

def ex2prime : Datum :=
  { id := "chomsky2015_ex2prime"
    source := ⟨"chomsky-2015", "(2′)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who do you think that read the book?"
    glossedTokens := []
    context := "The subject moved on from the specifier of T to the matrix clause, with the complementizer present."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("structure", "subjectExtracted")] }

def ex3 : Datum :=
  { id := "chomsky2015_ex3"
    source := ⟨"chomsky-2015", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They expected John to win."
    glossedTokens := []
    context := "Raising to object: the embedded subject raised to the specifier of the root expect."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "objectRaised")] }

def ex3prime : Datum :=
  { id := "chomsky2015_ex3prime"
    source := ⟨"chomsky-2015", "(3′)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who do you expect to win?"
    glossedTokens := []
    context := "The raised object extracted further to the matrix clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "objectExtracted")] }

def ex4 : Datum :=
  { id := "chomsky2015_ex4"
    source := ⟨"chomsky-2015", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who do you think read the book?"
    glossedTokens := []
    context := "The subject extracted with the complementizer deleted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "subjectExtractedNoC")] }

def all : List Datum := [ex1, ex2, ex2prime, ex3, ex3prime, ex4]

end Chomsky2015.Examples
