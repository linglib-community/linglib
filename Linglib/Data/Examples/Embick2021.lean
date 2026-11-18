module

public import Linglib.Data.Examples.Schema

/-!
# `Embick2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Embick2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Embick2021.Examples`.
-/

@[expose] public section

namespace Embick2021.Examples

def ex_6c : Datum :=
  { id := "embick2021_6c"
    source := ⟨"embick-2021", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's destruction of the city"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "DESTROY"), ("rootClass", "agentive"), ("construction", "derivedNominal"), ("h1", "n"), ("h1exp", "-tion")] }

def ex_6d : Datum :=
  { id := "embick2021_6d"
    source := ⟨"embick-2021", "(6d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's destroying the city"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "DESTROY"), ("rootClass", "agentive"), ("construction", "gerund"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", ""), ("h3", "n"), ("h3exp", "-ing")] }

def ex_7c : Datum :=
  { id := "embick2021_7c"
    source := ⟨"embick-2021", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's growth of tomatoes"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("root", "GROW"), ("rootClass", "nonagentive"), ("construction", "derivedNominal"), ("h1", "n"), ("h1exp", "-th")] }

def ex_7d : Datum :=
  { id := "embick2021_7d"
    source := ⟨"embick-2021", "(7d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's growing tomatoes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "GROW"), ("rootClass", "nonagentive"), ("construction", "gerund"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", ""), ("h3", "n"), ("h3exp", "-ing")] }

def bent : Datum :=
  { id := "embick2021_bent"
    source := ⟨"embick-2021", "§5, structure (15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "ben-t"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "BEND"), ("construction", "inflected"), ("h1", "v"), ("h1exp", ""), ("h2", "T"), ("h2exp", "-t")] }

def broken : Datum :=
  { id := "embick2021_broken"
    source := ⟨"embick-2021", "§5, structure (15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "brok-en"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "BREAK"), ("construction", "inflected"), ("h1", "v"), ("h1exp", ""), ("h2", "aspect"), ("h2exp", "-en")] }

def all : List Datum := [ex_6c, ex_6d, ex_7c, ex_7d, bent, broken]

end Embick2021.Examples
