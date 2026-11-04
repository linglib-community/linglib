module

public import Linglib.Data.Examples.Schema

/-!
# `Hofmann2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Hofmann2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hofmann2025.Examples`.
-/

@[expose] public section

namespace Hofmann2025.Examples

def ex1a : Datum :=
  { id := "hofmann2025_ex1a"
    source := ⟨"hofmann-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary owns a car. It is red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "veridical"), ("anaphor", "veridical")] }

def ex1b : Datum :=
  { id := "hofmann2025_ex1b"
    source := ⟨"hofmann-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't own a car. It is red."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "counterfactual"), ("anaphor", "veridical")] }

def ex2a : Datum :=
  { id := "hofmann2025_ex2a"
    source := ⟨"krahmer-muskens-1995", "(5)"⟩
    reportedIn := some ⟨"hofmann-2025", "(2a)"⟩
    language := "stan1293"
    primaryText := "It's not true that John didn't bring an umbrella. It was purple and stood in the hallway."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "veridical"), ("anaphor", "veridical"), ("case", "double negation")] }

def ex2b : Datum :=
  { id := "hofmann2025_ex2b"
    source := ⟨"roberts-1989", "(12)"⟩
    reportedIn := some ⟨"hofmann-2025", "(2b)"⟩
    language := "stan1293"
    primaryText := "Either there isn't a bathroom in this house or it's in a funny place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("antecedent", "hypothetical"), ("anaphor", "nonveridical"), ("case", "bathroom disjunction")] }

def ex2c : Datum :=
  { id := "hofmann2025_ex2c"
    source := ⟨"hofmann-2025", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: There isn't a bathroom in this house. B: (What are you talking about?) It is just in a weird place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "counterfactual"), ("anaphor", "veridical"), ("case", "disagreement")] }

def ex2d : Datum :=
  { id := "hofmann2025_ex2d"
    source := ⟨"frank-1996", "(8a)"⟩
    reportedIn := some ⟨"hofmann-2025", "(2d)"⟩
    language := "stan1293"
    primaryText := "Fred didn't buy a microwave oven. He wouldn't know what to do with it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical"), ("case", "modal subordination")] }

def ex5a : Datum :=
  { id := "hofmann2025_ex5a"
    source := ⟨"hofmann-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill didn't realize that he had a dime. It was in his pocket."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "veridical"), ("anaphor", "veridical")] }

def ex5b : Datum :=
  { id := "hofmann2025_ex5b"
    source := ⟨"hofmann-2025", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John forgot not to bring an umbrella, but we had no room for it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "veridical"), ("anaphor", "veridical")] }

def ex6a : Datum :=
  { id := "hofmann2025_ex6a"
    source := ⟨"hofmann-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't own a car. It is parked outside."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "counterfactual"), ("anaphor", "veridical")] }

def ex6b : Datum :=
  { id := "hofmann2025_ex6b"
    source := ⟨"hofmann-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't own a car. It would be parked outside."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical")] }

def ex6c : Datum :=
  { id := "hofmann2025_ex6c"
    source := ⟨"hofmann-2025", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't own a car, even though Cole said that it's red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical")] }

def ex8a : Datum :=
  { id := "hofmann2025_ex8a"
    source := ⟨"roberts-1989", "(11)"⟩
    reportedIn := some ⟨"hofmann-2025", "(8a)"⟩
    language := "stan1293"
    primaryText := "A wolf might walk in. It is gray."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("antecedent", "hypothetical"), ("anaphor", "veridical")] }

def ex8b : Datum :=
  { id := "hofmann2025_ex8b"
    source := ⟨"roberts-1989", "(11)"⟩
    reportedIn := some ⟨"hofmann-2025", "(8b)"⟩
    language := "stan1293"
    primaryText := "A wolf might walk in. It would eat you first."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("antecedent", "hypothetical"), ("anaphor", "nonveridical")] }

def ex9 : Datum :=
  { id := "hofmann2025_ex9"
    source := ⟨"hofmann-2025", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that there isn't a bathroom in this house. It's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("antecedent", "veridical"), ("anaphor", "veridical"), ("case", "double negation")] }

def ex10 : Datum :=
  { id := "hofmann2025_ex10"
    source := ⟨"hofmann-2025", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there isn't a bathroom in this house or it's in a weird place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("antecedent", "hypothetical"), ("anaphor", "nonveridical"), ("case", "bathroom disjunction")] }

def ex11 : Datum :=
  { id := "hofmann2025_ex11"
    source := ⟨"hofmann-2025", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a bathroom in this house. It would be easier to find."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical"), ("case", "modal subordination")] }

def ex12 : Datum :=
  { id := "hofmann2025_ex12"
    source := ⟨"hofmann-2025", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: There isn't a bathroom in this house. B: (What are you talking about?) It's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("antecedent", "counterfactual"), ("anaphor", "veridical"), ("case", "disagreement")] }

def ex13a : Datum :=
  { id := "hofmann2025_ex13a"
    source := ⟨"hofmann-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "S: Mary doesn't own a car, even though Cole said that it's red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical")] }

def ex13b : Datum :=
  { id := "hofmann2025_ex13b"
    source := ⟨"hofmann-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "S: Mary doesn't own a car, even though Cole knows that it's red."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("antecedent", "counterfactual"), ("anaphor", "veridical")] }

def ex15 : Datum :=
  { id := "hofmann2025_ex15"
    source := ⟨"hofmann-2025", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't have a car, so he doesn't have to wash it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical")] }

def ex18ac : Datum :=
  { id := "hofmann2025_ex18ac"
    source := ⟨"hofmann-2025", "(18a), (18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a bathroom here. It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("antecedent", "veridical"), ("anaphor", "veridical")] }

def ex18bc : Datum :=
  { id := "hofmann2025_ex18bc"
    source := ⟨"hofmann-2025", "(18b), (18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a bathroom here. It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("antecedent", "counterfactual"), ("anaphor", "veridical")] }

def ex26 : Datum :=
  { id := "hofmann2025_ex26"
    source := ⟨"hofmann-2025", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a bathroom. It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("antecedent", "counterfactual"), ("anaphor", "veridical")] }

def ex42a : Datum :=
  { id := "hofmann2025_ex42a"
    source := ⟨"hofmann-2025", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that there isn't a bathroom. It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("antecedent", "veridical"), ("anaphor", "veridical"), ("case", "double negation")] }

def ex42b : Datum :=
  { id := "hofmann2025_ex42b"
    source := ⟨"hofmann-2025", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there isn't a bathroom, or it is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("antecedent", "hypothetical"), ("anaphor", "nonveridical"), ("case", "bathroom disjunction")] }

def ex42c : Datum :=
  { id := "hofmann2025_ex42c"
    source := ⟨"hofmann-2025", "(42c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: There isn't a bathroom. B: It is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("antecedent", "counterfactual"), ("anaphor", "veridical"), ("case", "disagreement")] }

def ex42d : Datum :=
  { id := "hofmann2025_ex42d"
    source := ⟨"hofmann-2025", "(42d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a bathroom. It would be upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical"), ("case", "modal subordination")] }

def ex45 : Datum :=
  { id := "hofmann2025_ex45"
    source := ⟨"hofmann-2025", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there is a bathroom in this house, or it's upstairs."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("case", "inclusive disjunction")] }

def ex49 : Datum :=
  { id := "hofmann2025_ex49"
    source := ⟨"hofmann-2025", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a bathroom in this house, but Sue still hopes/believes it's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical"), ("case", "modal subordination")] }

def ex51 : Datum :=
  { id := "hofmann2025_ex51"
    source := ⟨"hofmann-2025", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a bathroom. Sue believes it's upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("antecedent", "counterfactual"), ("anaphor", "nonveridical"), ("case", "modal subordination")] }

def all : List Datum := [ex1a, ex1b, ex2a, ex2b, ex2c, ex2d, ex5a, ex5b, ex6a, ex6b, ex6c, ex8a, ex8b, ex9, ex10, ex11, ex12, ex13a, ex13b, ex15, ex18ac, ex18bc, ex26, ex42a, ex42b, ex42c, ex42d, ex45, ex49, ex51]

end Hofmann2025.Examples
