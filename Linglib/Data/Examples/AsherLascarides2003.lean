module

public import Linglib.Data.Examples.Schema

/-!
# `AsherLascarides2003` — typed example data

Auto-generated from `Linglib/Data/Examples/AsherLascarides2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AsherLascarides2003.Examples`.
-/

@[expose] public section

namespace AsherLascarides2003.Examples

def ex_18 : Datum :=
  { id := "asherlascarides2003_18"
    source := ⟨"asher-lascarides-2003", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had a great evening last night. He had a great meal. He ate salmon. He devoured lots of cheese. He then won a dancing competition."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "(17)")] }

def ex_18_pink : Datum :=
  { id := "asherlascarides2003_18_pink"
    source := ⟨"asher-lascarides-2003", "(18), p. 147 continuation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had a great evening last night. He had a great meal. He ate salmon. He devoured lots of cheese. He then won a dancing competition. It was a beautiful pink."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "(17)"), ("antecedent", "salmon"), ("antecedentLabel", "3")] }

def ex_19 : Datum :=
  { id := "asherlascarides2003_19"
    source := ⟨"asher-lascarides-2003", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John bought an apartment but he rented it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relations", "Contrast, Narration")] }

def ex_22 : Datum :=
  { id := "asherlascarides2003_22"
    source := ⟨"asher-lascarides-2003", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drives a car. It is red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relations", "Background"), ("antecedent", "car")] }

def ex_23 : Datum :=
  { id := "asherlascarides2003_23"
    source := ⟨"asher-lascarides-2003", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a farmer doesn't drive a car then it's red."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relations", "Consequence"), ("antecedent", "car")] }

def all : List Datum := [ex_18, ex_18_pink, ex_19, ex_22, ex_23]

end AsherLascarides2003.Examples
