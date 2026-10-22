module

public import Linglib.Data.Examples.Schema

/-!
# `Chomsky2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Chomsky2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chomsky2013.Examples`.
-/

@[expose] public section

namespace Chomsky2013.Examples

def ex20 : Datum :=
  { id := "chomsky2013_ex20"
    source := ⟨"chomsky-2013", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They thought JFK was assassinated in which Texas city?"
    glossedTokens := []
    context := "Asking a question in a quiz show, where the wh-phrase stays in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "whInSitu")] }

def ex21 : Datum :=
  { id := "chomsky2013_ex21"
    source := ⟨"chomsky-2013", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They thought in which Texas city JFK was assassinated?"
    glossedTokens := []
    context := "The wh-phrase stops at the edge of the embedded declarative CP, with the interpretation of (20)."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("structure", "whAtDeclarativeEdge")] }

def ex22 : Datum :=
  { id := "chomsky2013_ex22"
    source := ⟨"chomsky-2013", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They wondered in which Texas city JFK was assassinated."
    glossedTokens := []
    context := "An indirect question: the wh-phrase at the edge of an interrogative CP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "whAtInterrogativeEdge")] }

def all : List Datum := [ex20, ex21, ex22]

end Chomsky2013.Examples
