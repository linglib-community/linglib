module

public import Linglib.Data.Examples.Schema

/-!
# `VanTielEtAl2021` — typed example data

Auto-generated from `Linglib/Data/Examples/VanTielEtAl2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanTielEtAl2021.Examples`.
-/

@[expose] public section

namespace VanTielEtAl2021.Examples

def frame : Datum :=
  { id := "vantieletal2021_frame"
    source := ⟨"van-tiel-franke-sauerland-2021", "Exp. 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "— of the circles are red."
    glossedTokens := []
    context := "A display of 432 red or black circles; the participant completes the frame with a quantity word, numerals discouraged."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("task", "production"), ("words", "17 quantity words, 87% of the data")] }

def all_inference : Datum :=
  { id := "vantieletal2021_all_inference"
    source := ⟨"van-tiel-franke-sauerland-2021", "monotonicity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All guests ate salmon. → All guests ate fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("monotonicity", "increasing"), ("inference", "sets to supersets")] }

def no_inference : Datum :=
  { id := "vantieletal2021_no_inference"
    source := ⟨"van-tiel-franke-sauerland-2021", "monotonicity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No guest ate fish. → No guest ate salmon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("monotonicity", "decreasing"), ("inference", "sets to subsets")] }

def some_good : Datum :=
  { id := "vantieletal2021_some_good"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people liked the food, which is good."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("word", "some"), ("argumentative direction", "positive")] }

def some_bad : Datum :=
  { id := "vantieletal2021_some_bad"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people liked the food, which is bad."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("word", "some"), ("argumentative direction", "positive")] }

def few_bad : Datum :=
  { id := "vantieletal2021_few_bad"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few people liked the food, which is bad."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("word", "few"), ("argumentative direction", "negative")] }

def few_good : Datum :=
  { id := "vantieletal2021_few_good"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few people liked the food, which is good."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("word", "few"), ("argumentative direction", "negative")] }

def all : List Datum := [frame, all_inference, no_inference, some_good, some_bad, few_bad, few_good]

end VanTielEtAl2021.Examples
