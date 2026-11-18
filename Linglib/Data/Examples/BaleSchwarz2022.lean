module

public import Linglib.Data.Examples.Schema

/-!
# `BaleSchwarz2022` — typed example data

Auto-generated from `Linglib/Data/Examples/BaleSchwarz2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BaleSchwarz2022.Examples`.
-/

@[expose] public section

namespace BaleSchwarz2022.Examples

def bs2022_3 : Datum :=
  { id := "bs2022_3"
    source := ⟨"bale-schwarz-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sample weighs 0.9 grams."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "measurement verb"), ("numeral", "0.9"), ("unit", "grams")] }

def bs2022_6 : Datum :=
  { id := "bs2022_6"
    source := ⟨"bale-schwarz-2022", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sample weighs 0.9 grams per milliliter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "measurement verb"), ("numeral", "0.9"), ("unit", "grams"), ("per_unit", "milliliter"), ("unit_sensitivity", "the sample's volume is at least 1 milliliter")] }

def bs2022_10 : Datum :=
  { id := "bs2022_10"
    source := ⟨"bale-schwarz-2022", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This cube weighs what that cube weighs."
    glossedTokens := []
    context := "This cube weighs 1 kg while that cube weighs 2 kg."
    judgment := .acceptable
    contrasts := []
    readings := [("same weight", .acceptable), ("same density", .unacceptable)]
    paperFeatures := [("construction", "free relative")] }

def bs2022_14a : Datum :=
  { id := "bs2022_14a"
    source := ⟨"bale-schwarz-2022", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This cube weighs more than that cube weighs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("comparing weight", .acceptable), ("comparing density", .unacceptable)]
    paperFeatures := [("construction", "comparative")] }

def bs2022_14b : Datum :=
  { id := "bs2022_14b"
    source := ⟨"bale-schwarz-2022", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What does this cube weigh?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("asking for weight", .acceptable), ("asking for density", .unacceptable)]
    paperFeatures := [("construction", "wh-interrogative")] }

def bs2022_23a : Datum :=
  { id := "bs2022_23a"
    source := ⟨"bale-schwarz-2022", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mixture contains 0.9 grams of salt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("numeral", "0.9"), ("unit", "grams"), ("measure_function", "weight")] }

def bs2022_23b : Datum :=
  { id := "bs2022_23b"
    source := ⟨"bale-schwarz-2022", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mixture contains 0.8 milliliters of salt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("numeral", "0.8"), ("unit", "milliliters"), ("measure_function", "volume")] }

def bs2022_27 : Datum :=
  { id := "bs2022_27"
    source := ⟨"bale-schwarz-2022", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mixture contains 0.1 grams per milliliter of salt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("The mixture contains 0.1 grams of salt per milliliter.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("numeral", "0.1"), ("unit", "grams"), ("per_unit", "milliliter"), ("unit_sensitivity", "the mixture's volume is at least 1 milliliter")] }

def bs2022_33 : Datum :=
  { id := "bs2022_33"
    source := ⟨"bale-schwarz-2022", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much salt does the mixture contain?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("asking for absolute weight or volume", .acceptable), ("asking for concentration", .acceptable)]
    paperFeatures := [("construction", "wh-interrogative"), ("measure_function", "underspecified")] }

def bs2022_34 : Datum :=
  { id := "bs2022_34"
    source := ⟨"bale-schwarz-2022", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Amy knows how much salt the mixture contains."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("knowing the absolute weight or volume", .acceptable), ("knowing the concentration", .acceptable)]
    paperFeatures := [("construction", "embedded question"), ("measure_function", "underspecified")] }

def bs2022_36a : Datum :=
  { id := "bs2022_36a"
    source := ⟨"bale-schwarz-2022", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mixture contains 0.1 kilograms per liter of salt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("numeral", "0.1"), ("unit", "kilograms"), ("per_unit", "liter"), ("unit_sensitivity", "the mixture's volume is at least 1 liter")] }

def bs2022_37 : Datum :=
  { id := "bs2022_37"
    source := ⟨"bale-schwarz-2022", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The 5 milliliter sample of mixture contained 0.1 grams of salt per milliliter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("subject_measure", "5"), ("subject_unit", "milliliter"), ("numeral", "0.1"), ("unit", "grams"), ("per_unit", "milliliter"), ("unit_sensitivity", "5 mL ≥ mL")] }

def bs2022_38a : Datum :=
  { id := "bs2022_38a"
    source := ⟨"bale-schwarz-2022", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The 5 milliliter sample of mixture contained 0.1 grams of salt per liter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("subject_measure", "5"), ("subject_unit", "milliliter"), ("numeral", "0.1"), ("unit", "grams"), ("per_unit", "liter"), ("unit_sensitivity", "5 mL ≥ L")] }

def bs2022_38b : Datum :=
  { id := "bs2022_38b"
    source := ⟨"bale-schwarz-2022", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The 0.1 milliliter sample of mixture contained 0.1 grams of salt per milliliter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("subject_measure", "0.1"), ("subject_unit", "milliliter"), ("numeral", "0.1"), ("unit", "grams"), ("per_unit", "milliliter"), ("unit_sensitivity", "0.1 mL ≥ mL")] }

def bs2022_39a : Datum :=
  { id := "bs2022_39a"
    source := ⟨"bale-schwarz-2022", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The monograph by Dole contained more than 3 typos per page."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("per_unit", "page"), ("unit_sensitivity", "a monograph has at least one page")] }

def bs2022_39b : Datum :=
  { id := "bs2022_39b"
    source := ⟨"bale-schwarz-2022", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paragraph by Dole contained more than 3 typos per line."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("per_unit", "line"), ("unit_sensitivity", "a paragraph has at least one line")] }

def bs2022_40 : Datum :=
  { id := "bs2022_40"
    source := ⟨"bale-schwarz-2022", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paragraph by Dole contained more than 3 typos per page."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pseudo-partitive"), ("per_unit", "page"), ("unit_sensitivity", "a paragraph comprises less than a whole page")] }

def bs2022_44 : Datum :=
  { id := "bs2022_44"
    source := ⟨"bale-schwarz-2022", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The 5 milliliter portion of solution weighed 0.9 grams per milliliter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "measurement verb"), ("subject_measure", "5"), ("subject_unit", "milliliter"), ("numeral", "0.9"), ("unit", "grams"), ("per_unit", "milliliter"), ("unit_sensitivity", "5 mL ≥ mL")] }

def bs2022_45a : Datum :=
  { id := "bs2022_45a"
    source := ⟨"bale-schwarz-2022", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The 5 milliliter portion of solution weighed 0.9 kilograms per liter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "measurement verb"), ("subject_measure", "5"), ("subject_unit", "milliliter"), ("numeral", "0.9"), ("unit", "kilograms"), ("per_unit", "liter"), ("unit_sensitivity", "5 mL ≥ L")] }

def bs2022_45b : Datum :=
  { id := "bs2022_45b"
    source := ⟨"bale-schwarz-2022", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The 0.1 milliliter portion of solution weighed 0.9 grams per milliliter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "measurement verb"), ("subject_measure", "0.1"), ("subject_unit", "milliliter"), ("numeral", "0.9"), ("unit", "grams"), ("per_unit", "milliliter"), ("unit_sensitivity", "0.1 mL ≥ mL")] }

def bs2022_46 : Datum :=
  { id := "bs2022_46"
    source := ⟨"bale-schwarz-2022", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sample's density is 0.9 grams per milliliter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "copular"), ("numeral", "0.9"), ("unit", "grams"), ("per_unit", "milliliter")] }

def bs2022_47 : Datum :=
  { id := "bs2022_47"
    source := ⟨"bale-schwarz-2022", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sample's density is 0.9 grams."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "copular"), ("numeral", "0.9"), ("unit", "grams")] }

def bs2022_48 : Datum :=
  { id := "bs2022_48"
    source := ⟨"bale-schwarz-2022", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sample's density is 0.9 grams for every cubic centimeter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "copular"), ("numeral", "0.9"), ("unit", "grams"), ("quantifier", "for every")] }

def bs2022_49 : Datum :=
  { id := "bs2022_49"
    source := ⟨"bale-schwarz-2022", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "London's population density is 968 people for every km²."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "copular"), ("numeral", "968"), ("unit", "people"), ("quantifier", "for every")] }

def all : List Datum := [bs2022_3, bs2022_6, bs2022_10, bs2022_14a, bs2022_14b, bs2022_23a, bs2022_23b, bs2022_27, bs2022_33, bs2022_34, bs2022_36a, bs2022_37, bs2022_38a, bs2022_38b, bs2022_39a, bs2022_39b, bs2022_40, bs2022_44, bs2022_45a, bs2022_45b, bs2022_46, bs2022_47, bs2022_48, bs2022_49]

end BaleSchwarz2022.Examples
