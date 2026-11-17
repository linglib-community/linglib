module

public import Linglib.Data.Examples.Schema

/-!
# `RonderosEtAl2024` — typed example data

Auto-generated from `Linglib/Data/Examples/RonderosEtAl2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RonderosEtAl2024.Examples`.
-/

@[expose] public section

namespace RonderosEtAl2024.Examples

def ronderos2024_1a : Datum :=
  { id := "ronderos2024_1a"
    source := ⟨"ronderos-etal-2024", "Figure 1 (1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the short pencil"
    glossedTokens := []
    context := "Display: the target (short pencil), a long pencil, short scissors, and a distractor; three-second preview, then the description."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjType", "scalar"), ("condition", "contrast")] }

def ronderos2024_1b : Datum :=
  { id := "ronderos2024_1b"
    source := ⟨"ronderos-etal-2024", "Figure 1 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the short candle"
    glossedTokens := []
    context := "Display: the target (short candle) and three objects of other kinds (a pot, a glass, a chair)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjType", "scalar"), ("condition", "noContrast")] }

def ronderos2024_2a : Datum :=
  { id := "ronderos2024_2a"
    source := ⟨"ronderos-etal-2024", "Figure 1 (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the black lamp"
    glossedTokens := []
    context := "Display: the target (black lamp), a blue lamp, a black object of another kind, and a distractor; three-second preview, then the description."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjType", "color"), ("condition", "contrast")] }

def ronderos2024_2b : Datum :=
  { id := "ronderos2024_2b"
    source := ⟨"ronderos-etal-2024", "Figure 1 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the black drum"
    glossedTokens := []
    context := "Display: the target (black drum), a black object of another kind (a suitcase), and two distractors of other kinds."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjType", "color"), ("condition", "noContrast")] }

def ronderos2024_3a : Datum :=
  { id := "ronderos2024_3a"
    source := ⟨"ronderos-etal-2024", "Figure 1 (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the leather shoes"
    glossedTokens := []
    context := "Display: the target (leather shoes), canvas shoes, a leather object of another kind, and a distractor; three-second preview, then the description."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjType", "material"), ("condition", "contrast")] }

def ronderos2024_3b : Datum :=
  { id := "ronderos2024_3b"
    source := ⟨"ronderos-etal-2024", "Figure 1 (3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the leather bag"
    glossedTokens := []
    context := "Display: the target (leather bag), a leather object of another kind (boots), and two distractors of other kinds."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adjType", "material"), ("condition", "noContrast")] }

def all : List Datum := [ronderos2024_1a, ronderos2024_1b, ronderos2024_2a, ronderos2024_2b, ronderos2024_3a, ronderos2024_3b]

end RonderosEtAl2024.Examples
