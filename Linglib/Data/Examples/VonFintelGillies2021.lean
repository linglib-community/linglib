module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintelGillies2021` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintelGillies2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintelGillies2021.Examples`.
-/

@[expose] public section

namespace VonFintelGillies2021.Examples

def cant_possible : Datum :=
  { id := "vonfintelgillies2021_cant_possible"
    source := ⟨"von-fintel-gillies-2021", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it's possible the keys are in the drawer but they can't be."
    glossedTokens := []
    context := "Flat-footed conjunction of 'possible phi' with 'can't phi', embedded under suppose."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "cant_possible_contradiction"), ("modal", "cant")] }

def phil_dinner : Datum :=
  { id := "vonfintelgillies2021_phil_dinner"
    source := ⟨"von-fintel-gillies-2021", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinner must be ready."
    glossedTokens := []
    context := "Phil has cooked the dinner, checking all the food himself, and knows it is ready."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "direct"), ("must_entails_prejacent", "true")] }

def meryl_dinner : Datum :=
  { id := "vonfintelgillies2021_meryl_dinner"
    source := ⟨"von-fintel-gillies-2021", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinner must be ready."
    glossedTokens := []
    context := "Phil had to step out and instructed Meryl to turn the peas off when they are done and take the chicken out when the temperature is right; she does both and has seen that the table is set, but wonders whether Phil was planning to make anything else, e.g. a salad."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def all : List Datum := [cant_possible, phil_dinner, meryl_dinner]

end VonFintelGillies2021.Examples
