module

public import Linglib.Data.Examples.Schema

/-!
# `TesslerFranke2019` — typed example data

Auto-generated from `Linglib/Data/Examples/TesslerFranke2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TesslerFranke2019.Examples`.
-/

@[expose] public section

namespace TesslerFranke2019.Examples

def happy : Datum :=
  { id := "tesslerfranke2019_happy"
    source := ⟨"tessler-franke-2019", "Figure 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jones is happy."
    glossedTokens := []
    context := "Bare positive of the happy/unhappy quadruplet. Baseline against which the three negated forms are compared."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "positive"), ("inner_neg", "none"), ("cost", "0"), ("equivalent_to_positive", "true")] }

def unhappy : Datum :=
  { id := "tesslerfranke2019_unhappy"
    source := ⟨"tessler-franke-2019", "Figure 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jones is unhappy."
    glossedTokens := []
    context := "Figure 3: 'unhappy' could signal either contradictory negation ¬H ([un- [happy]], x ≤ θ1) or contrary negation H̃ ([unhappy], x ≤ θ2). In isolation (Experiment 1) morphological antonyms and negated positives (unhappy, not happy) receive the same ratings."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "negative"), ("inner_neg", "morphological"), ("cost", "2"), ("equivalent_to_positive", "false")] }

def not_happy : Datum :=
  { id := "tesslerfranke2019_not_happy"
    source := ⟨"tessler-franke-2019", "Figure 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jones is not happy."
    glossedTokens := []
    context := "Figure 3: 'not happy' could signal either contradictory negation ¬H ([not [happy]], x ≤ θ1) or contrary negation H̃ ([not happy], x ≤ θ2). In isolation (Experiment 1) negated positives and morphological antonyms (not happy, unhappy) receive the same ratings."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "notPositive"), ("inner_neg", "syntactic"), ("cost", "3"), ("equivalent_to_positive", "false")] }

def not_unhappy : Datum :=
  { id := "tesslerfranke2019_not_unhappy"
    source := ⟨"tessler-franke-2019", "Figure 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jones is not unhappy."
    glossedTokens := []
    context := "The paper's central observation: 'not unhappy' does NOT reduce to 'happy'. The inner morphological negation is contrary, so 'not unhappy' covers the gap region between the negative and positive thresholds, where 'happy' is false."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "notNegative"), ("inner_neg", "morphological"), ("cost", "5"), ("equivalent_to_positive", "false")] }

def all : List Datum := [happy, unhappy, not_happy, not_unhappy]

end TesslerFranke2019.Examples
