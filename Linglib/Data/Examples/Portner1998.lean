module

public import Linglib.Data.Examples.Schema

/-!
# `Portner1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Portner1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Portner1998.Examples`.
-/

@[expose] public section

namespace Portner1998.Examples

def ex11 : Datum :=
  { id := "portner1998_ex11"
    source := ⟨"portner-1998", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max was crossing the street."
    glossedTokens := []
    context := "Max does not in fact cross the street because a bus, cruising along P St. at thirty miles per hour, hits him."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex39 : Datum :=
  { id := "portner1998_ex39"
    source := ⟨"portner-1998", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max was walking into the path of an oncoming bus."
    glossedTokens := []
    context := "Max does not in fact cross the street because a bus, cruising along P St. at thirty miles per hour, hits him."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex18_ordinary : Datum :=
  { id := "portner1998_ex18_ordinary"
    source := ⟨"portner-1998", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was wiping out the Roman army."
    glossedTokens := []
    context := "Mary, an ordinary person, attacks the town barracks and fights whomever she sees; there is really no chance that she can wipe out the local garrison, much less the whole army."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex18_hero : Datum :=
  { id := "portner1998_ex18_hero"
    source := ⟨"portner-1998", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was wiping out the Roman army."
    glossedTokens := []
    context := "Mary, against all odds, actually succeeds in destroying the whole Roman army."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def all : List Datum := [ex11, ex39, ex18_ordinary, ex18_hero]

end Portner1998.Examples
