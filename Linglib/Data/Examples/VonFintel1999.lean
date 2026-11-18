module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintel1999` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintel1999.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintel1999.Examples`.
-/

@[expose] public section

namespace VonFintel1999.Examples

def ex10 : Datum :=
  { id := "vonfintel1999_ex10"
    source := ⟨"von-fintel-1999", "ex. 10, p. 101"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John ever ate any kale for breakfast."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "only John"), ("npi", "ever, any")] }

def ex21 : Datum :=
  { id := "vonfintel1999_ex21"
    source := ⟨"von-fintel-1999", "ex. 21, p. 107"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's been five years since I saw any bird of prey in this area."
    glossedTokens := []
    context := "Iatridou (p.c.) example relayed by von Fintel."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "since"), ("npi", "any")] }

def ex28a : Datum :=
  { id := "vonfintel1999_ex28a"
    source := ⟨"von-fintel-1999", "ex. 28a, p. 111"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy is amazed that Robin ever ate kale."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sandy is surprised that Robin ever ate kale.", .acceptable)]
    readings := []
    paperFeatures := [("licenser", "amazed/surprised"), ("npi", "ever")] }

def ex28b : Datum :=
  { id := "vonfintel1999_ex28b"
    source := ⟨"von-fintel-1999", "ex. 28b, p. 111"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy is sorry that Robin bought any car."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Sandy regrets that Robin bought any car.", .acceptable)]
    readings := []
    paperFeatures := [("licenser", "sorry/regret"), ("npi", "any")] }

def ex70a : Datum :=
  { id := "vonfintel1999_ex70a"
    source := ⟨"von-fintel-1999", "ex. 70a, p. 135"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John subscribes to any newspaper, he is probably well informed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("If he has ever told a lie, he must go to confession.", .acceptable), ("If you had left any later, you would have missed the plane.", .acceptable)]
    readings := []
    paperFeatures := [("licenser", "conditional antecedent"), ("npi", "any, ever")] }

def ex75 : Datum :=
  { id := "vonfintel1999_ex75"
    source := ⟨"von-fintel-1999", "ex. 75, p. 138"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma is the tallest girl to ever win the dance contest."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "superlative"), ("npi", "ever")] }

def all : List Datum := [ex10, ex21, ex28a, ex28b, ex70a, ex75]

end VonFintel1999.Examples
