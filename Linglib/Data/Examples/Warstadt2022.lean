module

public import Linglib.Data.Examples.Schema

/-!
# `Warstadt2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Warstadt2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Warstadt2022.Examples`.
-/

@[expose] public section

namespace Warstadt2022.Examples

def ex_1 : Datum :=
  { id := "warstadt2022_1"
    source := ⟨"warstadt-2022", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom doesn't have a green card."
    glossedTokens := []
    context := "Does Tom need a visa?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("presupposition", "Tom is a non-US citizen"), ("projection", "projects"), ("qud", "need visa")] }

def ex_2 : Datum :=
  { id := "warstadt2022_2"
    source := ⟨"warstadt-2022", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom doesn't have a green card."
    glossedTokens := []
    context := "Can Tom get a free drink? The local bar is giving free drinks to anyone with a green card."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("presupposition", "Tom is a non-US citizen"), ("projection", "absent"), ("qud", "free drink")] }

def ex_3 : Datum :=
  { id := "warstadt2022_3"
    source := ⟨"warstadt-2022", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the new hires has a green card."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("presupposition", "the new hires are non-US citizens"), ("projection", "universal")] }

def ex_4 : Datum :=
  { id := "warstadt2022_4"
    source := ⟨"warstadt-2022", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom is not an Olympic sprinter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("level", "species"), ("inference", "Tom is an athlete"), ("strength", "stronger")] }

def ex_5 : Datum :=
  { id := "warstadt2022_5"
    source := ⟨"warstadt-2022", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom is not a runner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("level", "genus"), ("inference", "Tom is an athlete"), ("strength", "weaker")] }

def ex_6 : Datum :=
  { id := "warstadt2022_6"
    source := ⟨"warstadt-2022", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom is an athlete."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("level", "family")] }

def ex_7 : Datum :=
  { id := "warstadt2022_7"
    source := ⟨"warstadt-2022", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did he recently stop smoking?"
    glossedTokens := []
    context := "Why is Tom chewing on his pencil?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "stop"), ("projection", "reduced")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end Warstadt2022.Examples
