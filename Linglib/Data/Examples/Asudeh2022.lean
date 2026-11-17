module

public import Linglib.Data.Examples.Schema

/-!
# `Asudeh2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Asudeh2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Asudeh2022.Examples`.
-/

@[expose] public section

namespace Asudeh2022.Examples

def ex_6 : Datum :=
  { id := "asudeh2022_6"
    source := ⟨"asudeh-2022", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex likes Blake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("premises", "likes, alex, blake")] }

def ex_14 : Datum :=
  { id := "asudeh2022_14"
    source := ⟨"asudeh-2022", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody loves somebody."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("premises", "love, every, some")] }

def fig2_finnish : Datum :=
  { id := "asudeh2022_fig2_finnish"
    source := ⟨"asudeh-2022", "Figure 2, Finnish"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Join vettä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("premises", "speaker, drink, water")] }

def fig2_english : Datum :=
  { id := "asudeh2022_fig2_english"
    source := ⟨"asudeh-2022", "Figure 2, English"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I drank water."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("premises", "speaker, drink, water")] }

def all : List Datum := [ex_6, ex_14, fig2_finnish, fig2_english]

end Asudeh2022.Examples
