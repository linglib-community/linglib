module

public import Linglib.Data.Examples.Schema

/-!
# `White2014` — typed example data

Auto-generated from `Linglib/Data/Examples/White2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace White2014.Examples`.
-/

@[expose] public section

namespace White2014.Examples

def ex_1 : Datum :=
  { id := "white2014_1"
    source := ⟨"white-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he took the trash out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite"), ("inference", "presupposes (2)")] }

def ex_2 : Datum :=
  { id := "white2014_2"
    source := ⟨"white-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to take the trash out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("inference", "entails (2)")] }

def ex_3 : Datum :=
  { id := "white2014_3"
    source := ⟨"white-2014", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo took out the trash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("role", "the embedded content")] }

def ex_4 : Datum :=
  { id := "white2014_4"
    source := ⟨"white-2014", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo didn't remember that he took the trash out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "negation"), ("inference", "still implies (2)")] }

def ex_5 : Datum :=
  { id := "white2014_5"
    source := ⟨"white-2014", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo didn't remember to take the trash out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "negation"), ("inference", "implies the negation of (2)")] }

def ex_6 : Datum :=
  { id := "white2014_6"
    source := ⟨"white-2014", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo hoped to take out the trash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hope"), ("complement", "infinitive")] }

def ex_7 : Datum :=
  { id := "white2014_7"
    source := ⟨"white-2014", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It turned out that Bo took out the trash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "turn out"), ("complement", "finite")] }

def ex_8 : Datum :=
  { id := "white2014_8"
    source := ⟨"white-2014", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he had to take the trash out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite with overt modal"), ("inference", "presupposes (7b)")] }

def ex_9 : Datum :=
  { id := "white2014_9"
    source := ⟨"white-2014", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to clean the kitchen, even though he wasn't allowed to."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "denial of obligation")] }

def ex_10 : Datum :=
  { id := "white2014_10"
    source := ⟨"white-2014", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he cleaned the kitchen, even though he wasn't allowed to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "denial of obligation")] }

def ex_11 : Datum :=
  { id := "white2014_11"
    source := ⟨"white-2014", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to go to the store and that Jo asked him to grab cereal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "coordination")] }

def ex_12 : Datum :=
  { id := "white2014_12"
    source := ⟨"white-2014", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to wash the dishes and Jo, that the dog needed a walk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "gapping")] }

def ex_13 : Datum :=
  { id := "white2014_13"
    source := ⟨"white-2014", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo wasn't supposed to go to the store."
    glossedTokens := []
    context := "In the same context as (9a)."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "detachability")] }

def ex_14 : Datum :=
  { id := "white2014_14"
    source := ⟨"white-2014", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to fill the bird feeder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "again")] }

def ex_15 : Datum :=
  { id := "white2014_15"
    source := ⟨"white-2014", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered that he had to fill the feeder."
    glossedTokens := []
    context := "Jo told Bo to fill the bird feeder. He remembered this but didn't fill it. The next week, she asked again."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "again"), ("previous", "remembering only")] }

def ex_16 : Datum :=
  { id := "white2014_16"
    source := ⟨"white-2014", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered that he had to fill the feeder."
    glossedTokens := []
    context := "Jo told Bo to fill the bird feeder. He forgot this, but noticed it was empty and filled it anyway. She told him to again the next week."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "again"), ("previous", "filling only")] }

def ex_17 : Datum :=
  { id := "white2014_17"
    source := ⟨"white-2014", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered to fill the feeder."
    glossedTokens := []
    context := "Jo told Bo to fill the bird feeder. He remembered that he had to, but didn't. The next week, she asked again."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "again"), ("previous", "remembering only")] }

def ex_18 : Datum :=
  { id := "white2014_18"
    source := ⟨"white-2014", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered to fill the feeder."
    glossedTokens := []
    context := "Jo told Bo to fill the bird feeder. He forgot this, but noticed it was empty and filled it anyway. She told him to again the next week."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "again"), ("previous", "filling only")] }

def ex_19 : Datum :=
  { id := "white2014_19"
    source := ⟨"white-2014", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again hoped to get a ticket."
    glossedTokens := []
    context := "Bo hoped to get a ticket to Jo's show. He couldn't, but when Jo came again..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hope"), ("test", "again"), ("previous", "hoping only")] }

def ex_20 : Datum :=
  { id := "white2014_20"
    source := ⟨"white-2014", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he had to take out the trash, but he didn't end up doing it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complement", "finite with overt modal"), ("inference", "no actuality entailment")] }

def ex_21 : Datum :=
  { id := "white2014_21"
    source := ⟨"white-2014", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo hoped to get coal in her stocking and that it would be inky black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hope"), ("test", "coordination")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21]

end White2014.Examples
