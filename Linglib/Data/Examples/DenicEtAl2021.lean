module

public import Linglib.Data.Examples.Schema

/-!
# `DenicEtAl2021` — typed example data

Auto-generated from `Linglib/Data/Examples/DenicEtAl2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DenicEtAl2021.Examples`.
-/

@[expose] public section

namespace DenicEtAl2021.Examples

def ex_1 : Datum :=
  { id := "denicetal2021_1"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This animal is a siamese cat. → This animal is a cat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "positive"), ("direction", "subsetToSuperset")] }

def ex_2 : Datum :=
  { id := "denicetal2021_2"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This animal isn't a cat. → This animal isn't a siamese cat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "negative"), ("direction", "supersetToSubset")] }

def ex_3 : Datum :=
  { id := "denicetal2021_3"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This animal isn't a cat at all."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "negative"), ("pi", "npi")] }

def ex_4 : Datum :=
  { id := "denicetal2021_4"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This animal is a cat at all."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "positive"), ("pi", "npi")] }

def ex_5 : Datum :=
  { id := "denicetal2021_5"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I drank some coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "positive"), ("pi", "ppi")] }

def ex_6 : Datum :=
  { id := "denicetal2021_6"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't drink some coffee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("some narrow scope under negation", .unacceptable), ("some wide scope over negation", .acceptable)]
    paperFeatures := [("environment", "negative"), ("pi", "ppi")] }

def ex_7 : Datum :=
  { id := "denicetal2021_7"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 12 aliens saw birds. / Exactly 12 aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "exactly12")] }

def ex_8 : Datum :=
  { id := "denicetal2021_8"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 12 aliens saw some birds. / Exactly 12 aliens saw any birds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "exactly12"), ("pi", "both")] }

def ex_9 : Datum :=
  { id := "denicetal2021_9"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 12 aliens saw some doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("some doves are such that exactly 12 aliens saw them", .acceptable)]
    paperFeatures := [("environment", "exactly12"), ("pi", "ppi")] }

def ex_11 : Datum :=
  { id := "denicetal2021_11"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each alien received a high score in all human IQ tests. → Aliens are very intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "training"), ("expected", "follows")] }

def ex_12 : Datum :=
  { id := "denicetal2021_12"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few aliens visited Paris. → All aliens visited the Eiffel Tower."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "training"), ("expected", "doesNotFollow")] }

def ex_13 : Datum :=
  { id := "denicetal2021_13"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pink aliens have scary teeth. → Pink aliens are the most terrifying."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "training"), ("expected", "intermediate")] }

def ex_14 : Datum :=
  { id := "denicetal2021_14"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The purple alien saw (some) birds. → The purple alien saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "positive"), ("direction", "supersetToSubset"), ("pi", "ppi")] }

def ex_15 : Datum :=
  { id := "denicetal2021_15"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every alien saw (some) birds. → Every alien saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "every"), ("direction", "supersetToSubset"), ("pi", "ppi")] }

def ex_16 : Datum :=
  { id := "denicetal2021_16"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Many aliens saw (some) birds. → Many aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "many"), ("direction", "supersetToSubset"), ("pi", "ppi")] }

def ex_17 : Datum :=
  { id := "denicetal2021_17"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The purple alien didn't see (any) birds. → The purple alien didn't see doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "negative"), ("direction", "supersetToSubset"), ("pi", "npi")] }

def ex_18 : Datum :=
  { id := "denicetal2021_18"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No alien saw (any) birds. → No alien saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "no"), ("direction", "supersetToSubset"), ("pi", "npi")] }

def ex_19 : Datum :=
  { id := "denicetal2021_19"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few aliens saw (any) birds. → Few aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "few"), ("direction", "supersetToSubset"), ("pi", "npi")] }

def ex_20 : Datum :=
  { id := "denicetal2021_20"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 12 aliens saw (some/any) birds. → Exactly 12 aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "exactly12"), ("direction", "supersetToSubset"), ("pi", "both")] }

def ex_21 : Datum :=
  { id := "denicetal2021_21"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only 12 aliens saw (some/any) birds. → Only 12 aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "only12"), ("direction", "supersetToSubset"), ("pi", "both")] }

def ex_22 : Datum :=
  { id := "denicetal2021_22"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every alien who did not see some doves is hairy. / Every alien who did not see any doves is hairy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "everyNot"), ("pi", "both")] }

def ex_23 : Datum :=
  { id := "denicetal2021_23"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every alien who did not see (some/any) doves is hairy. → Every alien who did not see birds is hairy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "everyNot"), ("direction", "subsetToSuperset"), ("pi", "both")] }

def ex_24 : Datum :=
  { id := "denicetal2021_24"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No alien spent a year without seeing (some/any) doves. → No alien spent a year without seeing birds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "noWithout"), ("direction", "subsetToSuperset"), ("pi", "both")] }

def ex_25 : Datum :=
  { id := "denicetal2021_25"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(25)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Exactly 12 aliens saw some doves. → Exactly 12 aliens saw some birds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "exactly12"), ("direction", "subsetToSuperset"), ("pi", "ppi")] }

def ex_26 : Datum :=
  { id := "denicetal2021_26"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every alien who did not see some doves is hairy. → Every alien who did not see birds is hairy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("some doves are such that every alien who didn't see them is hairy", .acceptable)]
    paperFeatures := [("environment", "everyNot"), ("direction", "subsetToSuperset"), ("pi", "ppi")] }

def ex_28 : Datum :=
  { id := "denicetal2021_28"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No aliens saw birds. → No aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "no"), ("direction", "supersetToSubset"), ("pi", "noPI")] }

def ex_29 : Datum :=
  { id := "denicetal2021_29"
    source := ⟨"denic-homer-rothschild-chemla-2021", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No aliens saw any birds. → No aliens saw doves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "no"), ("direction", "supersetToSubset"), ("pi", "npi")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_28, ex_29]

end DenicEtAl2021.Examples
