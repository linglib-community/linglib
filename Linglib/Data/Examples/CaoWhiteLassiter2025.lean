module

public import Linglib.Data.Examples.Schema

/-!
# `CaoWhiteLassiter2025` — typed example data

Auto-generated from `Linglib/Data/Examples/CaoWhiteLassiter2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CaoWhiteLassiter2025.Examples`.
-/

@[expose] public section

namespace CaoWhiteLassiter2025.Examples

def cwl2025_ex3a : Datum :=
  { id := "cwl2025_ex3a"
    source := ⟨"cao-white-lassiter-2025", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A CAT [...] caused himself [to] look as much as possible like a doctor..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "interchangeability"), ("pair", "fables_cat"), ("attested", "false")] }

def cwl2025_ex3b : Datum :=
  { id := "cwl2025_ex3b"
    source := ⟨"cao-white-lassiter-2025", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A CAT [...] made himself look as much as possible like a doctor..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "interchangeability"), ("pair", "fables_cat"), ("attested", "true")] }

def cwl2025_ex3c : Datum :=
  { id := "cwl2025_ex3c"
    source := ⟨"cao-white-lassiter-2025", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A CAT [...] forced himself [to] look as much as possible like a doctor..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "interchangeability"), ("pair", "fables_cat"), ("attested", "false")] }

def cwl2025_ex4a : Datum :=
  { id := "cwl2025_ex4a"
    source := ⟨"cao-white-lassiter-2025", "(4a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "He caused cancer in one woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "interchangeability"), ("pair", "cancer"), ("attested", "true")] }

def cwl2025_ex4b : Datum :=
  { id := "cwl2025_ex4b"
    source := ⟨"cao-white-lassiter-2025", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He made cancer [happen] in one woman."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "interchangeability"), ("pair", "cancer")] }

def cwl2025_ex4c : Datum :=
  { id := "cwl2025_ex4c"
    source := ⟨"cao-white-lassiter-2025", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He forced cancer [to happen] in one woman."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "interchangeability"), ("pair", "cancer")] }

def cwl2025_ex5a : Datum :=
  { id := "cwl2025_ex5a"
    source := ⟨"cao-white-lassiter-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I caused Martha to go to the gym by mentioning how the habit has helped me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "gradability"), ("pair", "gym_mention")] }

def cwl2025_ex5b : Datum :=
  { id := "cwl2025_ex5b"
    source := ⟨"cao-white-lassiter-2025", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I made Martha go to the gym by mentioning how the habit has helped me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "gradability"), ("pair", "gym_mention")] }

def cwl2025_ex5c : Datum :=
  { id := "cwl2025_ex5c"
    source := ⟨"cao-white-lassiter-2025", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I forced Martha to go to the gym by mentioning how the habit has helped me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "gradability"), ("pair", "gym_mention")] }

def cwl2025_ex6a : Datum :=
  { id := "cwl2025_ex6a"
    source := ⟨"cao-white-lassiter-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I caused Martha to go to the gym by criticizing her physical appearance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "gradability"), ("pair", "gym_criticize")] }

def cwl2025_ex6b : Datum :=
  { id := "cwl2025_ex6b"
    source := ⟨"cao-white-lassiter-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I made Martha go to the gym by criticizing her physical appearance."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "gradability"), ("pair", "gym_criticize")] }

def cwl2025_ex6c : Datum :=
  { id := "cwl2025_ex6c"
    source := ⟨"cao-white-lassiter-2025", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I forced Martha to go to the gym by criticizing her physical appearance."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "gradability"), ("pair", "gym_criticize")] }

def cwl2025_ex7a : Datum :=
  { id := "cwl2025_ex7a"
    source := ⟨"cao-white-lassiter-2025", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I caused Martha to go to the gym by holding her child hostage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "gradability"), ("pair", "gym_hostage")] }

def cwl2025_ex7b : Datum :=
  { id := "cwl2025_ex7b"
    source := ⟨"cao-white-lassiter-2025", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I made Martha go to the gym by holding her child hostage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "gradability"), ("pair", "gym_hostage")] }

def cwl2025_ex7c : Datum :=
  { id := "cwl2025_ex7c"
    source := ⟨"cao-white-lassiter-2025", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I forced Martha to go to the gym by holding her child hostage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "gradability"), ("pair", "gym_hostage")] }

def cwl2025_ex8a : Datum :=
  { id := "cwl2025_ex8a"
    source := ⟨"cao-white-lassiter-2025", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The child was made to get into the car, although she could've chosen to do otherwise."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "alternatives"), ("pair", "car")] }

def cwl2025_ex8b : Datum :=
  { id := "cwl2025_ex8b"
    source := ⟨"cao-white-lassiter-2025", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The child was forced to get into the car, although she could've chosen to do otherwise."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "alternatives"), ("pair", "car")] }

def cwl2025_ex9a : Datum :=
  { id := "cwl2025_ex9a"
    source := ⟨"cao-white-lassiter-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John caused the children to dance, but he didn't intend for the children to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "intention"), ("pair", "dance_intent")] }

def cwl2025_ex9b : Datum :=
  { id := "cwl2025_ex9b"
    source := ⟨"cao-white-lassiter-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John made the children dance, but he didn't intend for the children to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "intention"), ("pair", "dance_intent")] }

def cwl2025_ex9c : Datum :=
  { id := "cwl2025_ex9c"
    source := ⟨"cao-white-lassiter-2025", "(9c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John forced the children to dance, but he didn't intend for the children to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "intention"), ("pair", "dance_intent")] }

def cwl2025_ex10a : Datum :=
  { id := "cwl2025_ex10a"
    source := ⟨"cao-white-lassiter-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John accidentally caused the children to dance. He didn't intend for the children to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cause"), ("dimension", "intention"), ("pair", "dance_accident")] }

def cwl2025_ex10b : Datum :=
  { id := "cwl2025_ex10b"
    source := ⟨"cao-white-lassiter-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John accidentally made the children dance. He didn't intend for the children to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "intention"), ("pair", "dance_accident")] }

def cwl2025_ex10c : Datum :=
  { id := "cwl2025_ex10c"
    source := ⟨"cao-white-lassiter-2025", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John accidentally forced the children to dance. He didn't intend for the children to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "force"), ("dimension", "intention"), ("pair", "dance_accident")] }

def cwl2025_ex11a : Datum :=
  { id := "cwl2025_ex11a"
    source := ⟨"cao-white-lassiter-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pirate made the prisoner walk down the plank."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "make"), ("dimension", "sufficiency"), ("pair", "plank")] }

def cwl2025_ex11b : Datum :=
  { id := "cwl2025_ex11b"
    source := ⟨"cao-white-lassiter-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pirate let the prisoner walk down the plank."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "let"), ("dimension", "sufficiency"), ("pair", "plank")] }

def all : List Datum := [cwl2025_ex3a, cwl2025_ex3b, cwl2025_ex3c, cwl2025_ex4a, cwl2025_ex4b, cwl2025_ex4c, cwl2025_ex5a, cwl2025_ex5b, cwl2025_ex5c, cwl2025_ex6a, cwl2025_ex6b, cwl2025_ex6c, cwl2025_ex7a, cwl2025_ex7b, cwl2025_ex7c, cwl2025_ex8a, cwl2025_ex8b, cwl2025_ex9a, cwl2025_ex9b, cwl2025_ex9c, cwl2025_ex10a, cwl2025_ex10b, cwl2025_ex10c, cwl2025_ex11a, cwl2025_ex11b]

end CaoWhiteLassiter2025.Examples
