module

public import Linglib.Data.Examples.Schema

/-!
# `AlexandropoulouGotzner2024b` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexandropoulouGotzner2024b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexandropoulouGotzner2024b.Examples`.
-/

@[expose] public section

namespace AlexandropoulouGotzner2024b.Examples

def ag2024b_1 : Datum :=
  { id := "ag2024b_1"
    source := ⟨"alexandropoulou-gotzner-2024b", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not large"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("My apartment is small", .acceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "implicates")] }

def ag2024b_2 : Datum :=
  { id := "ag2024b_2"
    source := ⟨"alexandropoulou-gotzner-2024b", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not small"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("My apartment is large", .unacceptable)]
    paperFeatures := [("adjective", "small"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "does_not_implicate")] }

def ag2024b_5a : Datum :=
  { id := "ag2024b_5a"
    source := ⟨"alexandropoulou-gotzner-2024b", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not clean"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is dirty", .acceptable)]
    paperFeatures := [("adjective", "clean"), ("adjectiveType", "absolute"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "entails")] }

def ag2024b_5b : Datum :=
  { id := "ag2024b_5b"
    source := ⟨"alexandropoulou-gotzner-2024b", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not dirty"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is clean", .acceptable)]
    paperFeatures := [("adjective", "dirty"), ("adjectiveType", "absolute"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "entails")] }

def ag2024b_6a : Datum :=
  { id := "ag2024b_6a"
    source := ⟨"alexandropoulou-gotzner-2024b", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not large"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is small", .unacceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "does_not_entail")] }

def ag2024b_6b : Datum :=
  { id := "ag2024b_6b"
    source := ⟨"alexandropoulou-gotzner-2024b", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not small"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is large", .unacceptable)]
    paperFeatures := [("adjective", "small"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "does_not_entail")] }

def ag2024b_7a : Datum :=
  { id := "ag2024b_7a"
    source := ⟨"alexandropoulou-gotzner-2024b", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not very clean"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is dirty", .unacceptable)]
    paperFeatures := [("adjective", "clean"), ("modifier", "very"), ("adjectiveType", "absolute"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "does_not_entail")] }

def ag2024b_7b : Datum :=
  { id := "ag2024b_7b"
    source := ⟨"alexandropoulou-gotzner-2024b", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not pristine"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is filthy", .unacceptable), ("The apartment is dirty", .unacceptable)]
    paperFeatures := [("adjective", "pristine"), ("adjectiveType", "absolute"), ("strength", "strong"), ("polarity", "positive"), ("negation", "negated"), ("relation", "does_not_entail")] }

def ag2024b_9 : Datum :=
  { id := "ag2024b_9"
    source := ⟨"alexandropoulou-gotzner-2024b", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is large"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The apartment is large but not gigantic", .acceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "nonNegated"), ("relation", "implicates")] }

def ag2024b_10 : Datum :=
  { id := "ag2024b_10"
    source := ⟨"alexandropoulou-gotzner-2024b", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not large."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("My apartment is small", .acceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "implicates"), ("inference", "negative_strengthening")] }

def ag2024b_11 : Datum :=
  { id := "ag2024b_11"
    source := ⟨"alexandropoulou-gotzner-2024b", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not small."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("My apartment is neither large nor small", .acceptable)]
    paperFeatures := [("adjective", "small"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "implicates"), ("inference", "middling")] }

def all : List Datum := [ag2024b_1, ag2024b_2, ag2024b_5a, ag2024b_5b, ag2024b_6a, ag2024b_6b, ag2024b_7a, ag2024b_7b, ag2024b_9, ag2024b_10, ag2024b_11]

end AlexandropoulouGotzner2024b.Examples
