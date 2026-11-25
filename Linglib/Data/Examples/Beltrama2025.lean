module

public import Linglib.Data.Examples.Schema

/-!
# `Beltrama2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Beltrama2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beltrama2025.Examples`.
-/

@[expose] public section

namespace Beltrama2025.Examples

def ex_1a : Datum :=
  { id := "beltrama2025_1a"
    source := ⟨"beltrama-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is decent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("middling: positive but only moderately so", .acceptable)]
    paperFeatures := [("class", "MPA"), ("inference", "middling")] }

def ex_3c : Datum :=
  { id := "beltrama2025_3c"
    source := ⟨"beltrama-2025", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Can you recommend a place making a decent pizza around here? B: Mario's! Their pizza is really good!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "cancelability"), ("verdict", "middling inference is an implicature")] }

def ex_4c : Datum :=
  { id := "beltrama2025_4c"
    source := ⟨"beltrama-2025", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is decent—but it's not great."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "reinforceability")] }

def ex_5c : Datum :=
  { id := "beltrama2025_5c"
    source := ⟨"beltrama-2025", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every customer who thinks their pizza was decent will get a refund."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "DE suspension"), ("verdict", "no upper-bounded reading in the restrictor")] }

def ex_8a : Datum :=
  { id := "beltrama2025_8a"
    source := ⟨"beltrama-2025", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is decent for a US pizza; but for an Italian pizza, it wouldn't be."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "for-phrase"), ("property", "context-sensitivity")] }

def ex_11a : Datum :=
  { id := "beltrama2025_11a"
    source := ⟨"beltrama-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pizza is very/incredibly/super decent."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alsoJudged := [.questionable]
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "strong intensifiers"), ("property", "restricted gradability")] }

def ex_12a : Datum :=
  { id := "beltrama2025_12a"
    source := ⟨"beltrama-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pizza A is more decent than Pizza B."
    glossedTokens := []
    context := "Pizza A is exceptionally good."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "comparative"), ("property", "mildness retained in comparatives")] }

def ex_15a : Datum :=
  { id := "beltrama2025_15a"
    source := ⟨"beltrama-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is neither acceptable nor unacceptable."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "zone of indifference"), ("verdict", "near-contradiction")] }

def ex_21 : Datum :=
  { id := "beltrama2025_21"
    source := ⟨"beltrama-2025", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This pizza is barely decent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "barely"), ("property", "crisp boundary")] }

def ex_22a : Datum :=
  { id := "beltrama2025_22a"
    source := ⟨"beltrama-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ok, this pizza is acceptable. But a pizza any worse than this one—even by just a tiny bit—wouldn't be acceptable."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "crisp judgment")] }

def ex_24a : Datum :=
  { id := "beltrama2025_24a"
    source := ⟨"beltrama-2025", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pizza scene in this town is truly desperate—you can't find even a decent one."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "emphasis in DE"), ("parallel", "minimizers")] }

def ex_26a : Datum :=
  { id := "beltrama2025_26a"
    source := ⟨"beltrama-2025", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Joe is very low maintenance when it comes to pizza. It takes just a decent one to make him happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "minimal sufficiency exclusive")] }

def ex_39 : Datum :=
  { id := "beltrama2025_39"
    source := ⟨"beltrama-2025", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pizza is slightly decent."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "slightly"), ("verdict", "against the MinSAA analysis")] }

def ex_51b : Datum :=
  { id := "beltrama2025_51b"
    source := ⟨"beltrama-2025", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pizza A is more decent than Pizza B, but neither is decent. In fact, they're both really bad."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "comparative entailment"), ("verdict", "positive form not entailed")] }

def ex_70 : Datum :=
  { id := "beltrama2025_70"
    source := ⟨"beltrama-2025", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I heard that pizza sucks. B: Not at all. It's actually extremely decent!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "strong intensifier rescued"), ("condition", "significance excluded from the QUD")] }

def all : List Datum := [ex_1a, ex_3c, ex_4c, ex_5c, ex_8a, ex_11a, ex_12a, ex_15a, ex_21, ex_22a, ex_24a, ex_26a, ex_39, ex_51b, ex_70]

end Beltrama2025.Examples
