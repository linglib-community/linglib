module

public import Linglib.Data.Examples.Schema

/-!
# `Zwarts2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Zwarts2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zwarts2005.Examples`.
-/

@[expose] public section

namespace Zwarts2005.Examples

def ex_1a : Datum :=
  { id := "zwarts2005_1a"
    source := ⟨"zwarts-2005", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex swam for an hour"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "atelic")] }

def ex_1b : Datum :=
  { id := "zwarts2005_1b"
    source := ⟨"zwarts-2005", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex swam to the beach in an hour"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "to")] }

def ex_1c : Datum :=
  { id := "zwarts2005_1c"
    source := ⟨"zwarts-2005", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex swam towards the beach for an hour"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "atelic"), ("preposition", "towards")] }

def ex_12a : Datum :=
  { id := "zwarts2005_12a"
    source := ⟨"zwarts-2005", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex ran away from the accident"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "away from")] }

def ex_23a : Datum :=
  { id := "zwarts2005_23a"
    source := ⟨"zwarts-2005", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex ran to the house in a minute"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "to")] }

def ex_23b : Datum :=
  { id := "zwarts2005_23b"
    source := ⟨"zwarts-2005", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex walked over the bridge in two minutes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "over")] }

def ex_23c : Datum :=
  { id := "zwarts2005_23c"
    source := ⟨"zwarts-2005", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex crawled out of the room in three minutes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "out of")] }

def ex_30a : Datum :=
  { id := "zwarts2005_30a"
    source := ⟨"zwarts-2005", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex walk to the capitol"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "to")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_12a, ex_23a, ex_23b, ex_23c, ex_30a]

end Zwarts2005.Examples
