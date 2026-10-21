module

public import Linglib.Data.Examples.Schema

/-!
# `Koev2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Koev2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Koev2026.Examples`.
-/

@[expose] public section

namespace Koev2026.Examples

def ex_2 : Datum :=
  { id := "koev2026_2"
    source := ⟨"koev-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe the Patriots will win, but I'm not sure they will."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("contrast", "sure")] }

def ex_7 : Datum :=
  { id := "koev2026_7"
    source := ⟨"koev-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each [farmer] believes as strongly as the other that his crops will not survive another week without water, and each cares as much as the other about the survival of his crops."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("degreeConstruction", "equative")] }

def ex_8 : Datum :=
  { id := "koev2026_8"
    source := ⟨"koev-2026", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He believes more strongly than I do that the organization of the executive branch of the federal government matters a great deal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("degreeConstruction", "comparative")] }

def ex_9 : Datum :=
  { id := "koev2026_9"
    source := ⟨"koev-2026", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What group on this map most strongly believes that climate change is not real?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("degreeConstruction", "superlative")] }

def ex_10a : Datum :=
  { id := "koev2026_10a"
    source := ⟨"koev-2026", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No one believes more than me that fitness should be a top priority in our lives."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("degreeConstruction", "comparative")] }

def ex_10b : Datum :=
  { id := "koev2026_10b"
    source := ⟨"koev-2026", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What do you believe more, that the CIA killed JFK or that the government did 9/11?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("degreeConstruction", "comparative")] }

def ex_12a : Datum :=
  { id := "koev2026_12a"
    source := ⟨"koev-2026", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My boss fully believes that family comes first."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("modifier", "maximizer"), ("adverb", "fully")] }

def ex_12b : Datum :=
  { id := "koev2026_12b"
    source := ⟨"koev-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For one, I completely believe that Walmart is a monopoly, if you thought I was defending Walmart."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("modifier", "maximizer"), ("adverb", "completely")] }

def ex_12c : Datum :=
  { id := "koev2026_12c"
    source := ⟨"koev-2026", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "But Kathleen didn't entirely believe it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("modifier", "maximizer"), ("adverb", "entirely")] }

def multidim : Datum :=
  { id := "koev2026_multidim"
    source := ⟨"koev-2026", "§2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim believes in some respects that it is raining outside."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := [("Kim believes in most respects that it is raining outside.", .marginal), ("Kim believes in all respects that it is raining outside.", .marginal)]
    readings := []
    paperFeatures := [("predicate", "believe"), ("respects", "overt")] }

def fn4 : Datum :=
  { id := "koev2026_fn4"
    source := ⟨"koev-2026", "fn. 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John slightly believes that the Patriots will win."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := [("John believes a bit that the Patriots will win.", .questionable)]
    readings := []
    paperFeatures := [("predicate", "believe"), ("modifier", "minimizer"), ("adverb", "slightly")] }

def ex_13a : Datum :=
  { id := "koev2026_13a"
    source := ⟨"lassiter-2017", "p. 101"⟩
    reportedIn := some ⟨"koev-2026", "(13a)"⟩
    language := "stan1293"
    primaryText := "Bill is tall for a fourteen-year-old."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "tall"), ("comparisonClass", "overt")] }

def ex_13b : Datum :=
  { id := "koev2026_13b"
    source := ⟨"lassiter-2017", "p. 101"⟩
    reportedIn := some ⟨"koev-2026", "(13b)"⟩
    language := "stan1293"
    primaryText := "This room is full for a classroom."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "full"), ("comparisonClass", "overt")] }

def ex_14a : Datum :=
  { id := "koev2026_14a"
    source := ⟨"koev-2026", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Compared to an invasion of another neighboring country, an invasion of Ukraine is likely."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "likely"), ("comparisonClass", "overt")] }

def ex_14b : Datum :=
  { id := "koev2026_14b"
    source := ⟨"koev-2026", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Compared to an invasion of another neighboring country, I believe that Ukraine will be invaded."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "believe"), ("comparisonClass", "overt")] }

def fn6 : Datum :=
  { id := "koev2026_fn6"
    source := ⟨"koev-2026", "fn. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This glass is full for a wine glass."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "full"), ("comparisonClass", "overt")] }

def ex_15a : Datum :=
  { id := "koev2026_15a"
    source := ⟨"lassiter-2017", "p. 100"⟩
    reportedIn := some ⟨"koev-2026", "(15a)"⟩
    language := "stan1293"
    primaryText := "The rod is not bent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "bent"), ("antonym", "straight"), ("relation", "entails")] }

def ex_15b : Datum :=
  { id := "koev2026_15b"
    source := ⟨"lassiter-2017", "p. 100"⟩
    reportedIn := some ⟨"koev-2026", "(15b)"⟩
    language := "stan1293"
    primaryText := "The rod is not bent, but it is not straight either."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "bent"), ("antonym", "straight"), ("construction", "doubleDenial")] }

def ex_16a : Datum :=
  { id := "koev2026_16a"
    source := ⟨"lassiter-2017", "p. 100"⟩
    reportedIn := some ⟨"koev-2026", "(16a)"⟩
    language := "stan1293"
    primaryText := "Bill is not tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "tall"), ("antonym", "short"), ("relation", "does_not_entail")] }

def ex_16b : Datum :=
  { id := "koev2026_16b"
    source := ⟨"lassiter-2017", "p. 100"⟩
    reportedIn := some ⟨"koev-2026", "(16b)"⟩
    language := "stan1293"
    primaryText := "Bill is not tall, but he is not short either."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "tall"), ("antonym", "short"), ("construction", "doubleDenial")] }

def ex_17a : Datum :=
  { id := "koev2026_17a"
    source := ⟨"koev-2026", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jack doesn't doubt that Jill is at the party."
    glossedTokens := []
    context := "Jack is epistemically engaged with whether Jill is at the party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "doubt"), ("antonym", "believe"), ("relation", "entails")] }

def ex_17b : Datum :=
  { id := "koev2026_17b"
    source := ⟨"koev-2026", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jack doesn't believe that Jill is at the party, but he doesn't doubt it either."
    glossedTokens := []
    context := "Jack is epistemically engaged with whether Jill is at the party."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "believe"), ("antonym", "doubt"), ("construction", "doubleDenial")] }

def ex_18a : Datum :=
  { id := "koev2026_18a"
    source := ⟨"koev-2026", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jill is likely to be at the party."
    glossedTokens := []
    context := "The chance that Jill is at the party is exactly 50 percent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "likely"), ("truthValue", "false")] }

def ex_18b : Datum :=
  { id := "koev2026_18b"
    source := ⟨"koev-2026", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jill is unlikely to be at the party."
    glossedTokens := []
    context := "The chance that Jill is at the party is exactly 50 percent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "unlikely"), ("truthValue", "false")] }

def ex_19a : Datum :=
  { id := "koev2026_19a"
    source := ⟨"koev-2026", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 99 percent certain that Biden will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("It's 5 percent certain that Biden will win.", .questionable), ("It's 50 percent certain that Biden will win.", .marginal)]
    readings := []
    paperFeatures := [("predicate", "certain"), ("modifier", "percentage")] }

def ex_19b : Datum :=
  { id := "koev2026_19b"
    source := ⟨"koev-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 99 percent likely that Biden will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("It's 5 percent likely that Biden will win.", .marginal), ("It's 50 percent likely that Biden will win.", .acceptable)]
    readings := []
    paperFeatures := [("predicate", "likely"), ("modifier", "percentage")] }

def ex_20 : Datum :=
  { id := "koev2026_20"
    source := ⟨"koev-2026", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe 99 percent that Biden will win."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := [("I believe 5 percent that Biden will win.", .unacceptable), ("I believe 50 percent that Biden will win.", .unacceptable)]
    readings := []
    paperFeatures := [("predicate", "believe"), ("modifier", "percentage")] }

def fn10i : Datum :=
  { id := "koev2026_fn10i"
    source := ⟨"koev-2026", "fn. 10 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm sure she was at the party, but I don't know it."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "sure"), ("reading", "subjective")] }

def fn10ii : Datum :=
  { id := "koev2026_fn10ii"
    source := ⟨"koev-2026", "fn. 10 (ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was sure that the Patriots would win, and yet they lost."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "sure"), ("reading", "subjective")] }

def all : List Datum := [ex_2, ex_7, ex_8, ex_9, ex_10a, ex_10b, ex_12a, ex_12b, ex_12c, multidim, fn4, ex_13a, ex_13b, ex_14a, ex_14b, fn6, ex_15a, ex_15b, ex_16a, ex_16b, ex_17a, ex_17b, ex_18a, ex_18b, ex_19a, ex_19b, ex_20, fn10i, fn10ii]

end Koev2026.Examples
