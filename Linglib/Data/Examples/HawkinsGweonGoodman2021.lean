module

public import Linglib.Data.Examples.Schema

/-!
# `HawkinsGweonGoodman2021` — typed example data

Auto-generated from `Linglib/Data/Examples/HawkinsGweonGoodman2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HawkinsGweonGoodman2021.Examples`.
-/

@[expose] public section

namespace HawkinsGweonGoodman2021.Examples

def item1 : Datum :=
  { id := "hawkinsgweongoodman2021_item1"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 1"⟩
    language := "stan1293"
    primaryText := "Glasses"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "sunglasses"), ("hiddenDistractor", "glasses case"), ("condition", "scripted")] }

def item2 : Datum :=
  { id := "hawkinsgweongoodman2021_item2"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 2"⟩
    language := "stan1293"
    primaryText := "Bottom block"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "block (3rd row)"), ("hiddenDistractor", "block (4th row)"), ("condition", "scripted")] }

def item3 : Datum :=
  { id := "hawkinsgweongoodman2021_item3"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 3"⟩
    language := "stan1293"
    primaryText := "Tape"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "cassette"), ("hiddenDistractor", "Scotch tape"), ("condition", "scripted")] }

def item4 : Datum :=
  { id := "hawkinsgweongoodman2021_item4"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 4"⟩
    language := "stan1293"
    primaryText := "Large measuring cup"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "medium cup"), ("hiddenDistractor", "large cup"), ("condition", "scripted")] }

def item5 : Datum :=
  { id := "hawkinsgweongoodman2021_item5"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 5"⟩
    language := "stan1293"
    primaryText := "Brush"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "round hairbrush"), ("hiddenDistractor", "flat hairbrush"), ("condition", "scripted")] }

def item6 : Datum :=
  { id := "hawkinsgweongoodman2021_item6"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 6"⟩
    language := "stan1293"
    primaryText := "Eraser"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "board eraser"), ("hiddenDistractor", "pencil eraser"), ("condition", "scripted")] }

def item7 : Datum :=
  { id := "hawkinsgweongoodman2021_item7"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 7"⟩
    language := "stan1293"
    primaryText := "Small candle"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "medium candle"), ("hiddenDistractor", "small candle"), ("condition", "scripted")] }

def item8 : Datum :=
  { id := "hawkinsgweongoodman2021_item8"
    source := ⟨"keysar-etal-2003", ""⟩
    reportedIn := some ⟨"hawkins-gweon-goodman-2021", "Table 1, item 8"⟩
    language := "stan1293"
    primaryText := "Mouse"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("target", "computer mouse"), ("hiddenDistractor", "toy mouse"), ("condition", "scripted")] }

def shape : Datum :=
  { id := "hawkinsgweongoodman2021_shape"
    source := ⟨"hawkins-gweon-goodman-2021", "§2.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the square"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("features", "shape"), ("speaker", "egocentric")] }

def shapeColor : Datum :=
  { id := "hawkinsgweongoodman2021_shapeColor"
    source := ⟨"hawkins-gweon-goodman-2021", "§2.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the blue square"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("features", "shape, color")] }

def full : Datum :=
  { id := "hawkinsgweongoodman2021_full"
    source := ⟨"hawkins-gweon-goodman-2021", "§2.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the blue checked square"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("features", "shape, color, texture")] }

def all : List Datum := [item1, item2, item3, item4, item5, item6, item7, item8, shape, shapeColor, full]

end HawkinsGweonGoodman2021.Examples
