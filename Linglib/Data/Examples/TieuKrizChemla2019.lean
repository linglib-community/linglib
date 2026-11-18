module

public import Linglib.Data.Examples.Schema

/-!
# `TieuKrizChemla2019` — typed example data

Auto-generated from `Linglib/Data/Examples/TieuKrizChemla2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TieuKrizChemla2019.Examples`.
-/

@[expose] public section

namespace TieuKrizChemla2019.Examples

def ex_1 : Datum :=
  { id := "tieukrizchemla2019_1"
    source := ⟨"tieu-kriz-chemla-2019", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The trucks are blue."
    glossedTokens := []
    context := "Figure 1: the first and third trucks are blue, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := [("neither true nor false in the gap context", .acceptable)]
    paperFeatures := [("determiner", "the"), ("polarity", "positive"), ("context", "gap")] }

def ex_2 : Datum :=
  { id := "tieukrizchemla2019_2"
    source := ⟨"tieu-kriz-chemla-2019", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The trucks are not blue."
    glossedTokens := []
    context := "Figure 1: the first and third trucks are blue, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := [("neither true nor false in the gap context", .acceptable)]
    paperFeatures := [("determiner", "the"), ("polarity", "negative"), ("context", "gap")] }

def ex_3 : Datum :=
  { id := "tieukrizchemla2019_3"
    source := ⟨"tieu-kriz-chemla-2019", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the trucks are blue."
    glossedTokens := []
    context := "Figure 1: the first and third trucks are blue, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := [("false in the gap context", .acceptable)]
    paperFeatures := [("determiner", "all"), ("polarity", "positive"), ("context", "gap")] }

def ex_4 : Datum :=
  { id := "tieukrizchemla2019_4"
    source := ⟨"tieu-kriz-chemla-2019", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not all of the trucks are blue."
    glossedTokens := []
    context := "Figure 1: the first and third trucks are blue, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := [("true in the gap context", .acceptable)]
    paperFeatures := [("determiner", "all"), ("polarity", "negative"), ("context", "gap")] }

def ex_5a : Datum :=
  { id := "tieukrizchemla2019_5a"
    source := ⟨"tieu-kriz-chemla-2019", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The trucks are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("homogeneous", .acceptable), ("existential, as (6a)", .acceptable), ("universal, as (7a)", .acceptable)]
    paperFeatures := [("determiner", "the"), ("polarity", "positive")] }

def ex_5b : Datum :=
  { id := "tieukrizchemla2019_5b"
    source := ⟨"tieu-kriz-chemla-2019", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The trucks aren't blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("homogeneous", .acceptable), ("existential, as (6b)", .acceptable), ("universal, as (7b)", .acceptable)]
    paperFeatures := [("determiner", "the"), ("polarity", "negative")] }

def ex_6a : Datum :=
  { id := "tieukrizchemla2019_6a"
    source := ⟨"tieu-kriz-chemla-2019", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are some blue trucks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some"), ("polarity", "positive")] }

def ex_6b : Datum :=
  { id := "tieukrizchemla2019_6b"
    source := ⟨"tieu-kriz-chemla-2019", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There aren't any blue trucks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some"), ("polarity", "negative")] }

def ex_7a : Datum :=
  { id := "tieukrizchemla2019_7a"
    source := ⟨"tieu-kriz-chemla-2019", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every truck is blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("polarity", "positive")] }

def ex_7b : Datum :=
  { id := "tieukrizchemla2019_7b"
    source := ⟨"tieu-kriz-chemla-2019", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every truck is blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "every"), ("polarity", "negative")] }

def ex_8a : Datum :=
  { id := "tieukrizchemla2019_8a"
    source := ⟨"tieu-kriz-chemla-2019", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the trucks are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "some"), ("polarity", "positive")] }

def ex_8b : Datum :=
  { id := "tieukrizchemla2019_8b"
    source := ⟨"tieu-kriz-chemla-2019", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the trucks are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("polarity", "positive")] }

def ex_9a : Datum :=
  { id := "tieukrizchemla2019_9a"
    source := ⟨"tieu-kriz-chemla-2019", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the trucks are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("some but not all, the scalar implicature (9b)", .acceptable)]
    paperFeatures := [("determiner", "some"), ("polarity", "positive"), ("inference", "scalar implicature")] }

def ex_9b : Datum :=
  { id := "tieukrizchemla2019_9b"
    source := ⟨"tieu-kriz-chemla-2019", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not all of the trucks are blue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("polarity", "negative"), ("inference", "scalar implicature")] }

def ex_12a : Datum :=
  { id := "tieukrizchemla2019_12a"
    source := ⟨"tieu-kriz-chemla-2019", "(12a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les coeurs sont rouges."
    glossedTokens := []
    context := "Figure 3: the first and third hearts are red, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "the"), ("polarity", "positive"), ("context", "gap"), ("condition", "homogeneity target")] }

def ex_12b : Datum :=
  { id := "tieukrizchemla2019_12b"
    source := ⟨"tieu-kriz-chemla-2019", "(12b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les coeurs ne sont pas rouges."
    glossedTokens := []
    context := "Figure 3: the first and third hearts are red, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "the"), ("polarity", "negative"), ("context", "gap"), ("condition", "homogeneity target")] }

def ex_13a : Datum :=
  { id := "tieukrizchemla2019_13a"
    source := ⟨"tieu-kriz-chemla-2019", "(13a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les parapluies sont rouges."
    glossedTokens := []
    context := "Figure 4: all four umbrellas are red, or all four are blue."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "the"), ("polarity", "positive"), ("condition", "definite control")] }

def ex_13b : Datum :=
  { id := "tieukrizchemla2019_13b"
    source := ⟨"tieu-kriz-chemla-2019", "(13b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les parapluies ne sont pas rouges."
    glossedTokens := []
    context := "Figure 4: all four umbrellas are red, or all four are blue."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "the"), ("polarity", "negative"), ("condition", "definite control")] }

def ex_14a : Datum :=
  { id := "tieukrizchemla2019_14a"
    source := ⟨"tieu-kriz-chemla-2019", "(14a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Tous les coeurs sont rouges."
    glossedTokens := []
    context := "Figure 3: the first and third hearts are red, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("polarity", "positive"), ("context", "gap"), ("condition", "universal control")] }

def ex_14b : Datum :=
  { id := "tieukrizchemla2019_14b"
    source := ⟨"tieu-kriz-chemla-2019", "(14b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pas tous les coeurs sont rouges."
    glossedTokens := []
    context := "Figure 3: the first and third hearts are red, the second and fourth yellow."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("determiner", "all"), ("polarity", "negative"), ("context", "gap"), ("condition", "universal control")] }

def si_target : Datum :=
  { id := "tieukrizchemla2019_si_target"
    source := ⟨"tieu-kriz-chemla-2019", "Figure 5"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Certaines tentes sont oranges."
    glossedTokens := []
    context := "Figure 5: all four tents are orange."
    judgment := .acceptable
    contrasts := []
    readings := [("some but not all: rejected with the implicature", .acceptable), ("literal existential: accepted without the implicature", .acceptable)]
    paperFeatures := [("determiner", "some"), ("polarity", "positive"), ("context", "all"), ("condition", "scalar implicature target")] }

def ex_26 : Datum :=
  { id := "tieukrizchemla2019_26"
    source := ⟨"tieu-kriz-chemla-2019", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The townspeople are asleep."
    glossedTokens := []
    context := "A few insomniacs are reading in bed."
    judgment := .acceptable
    contrasts := []
    readings := [("non-maximal", .acceptable)]
    paperFeatures := [("determiner", "the"), ("polarity", "positive"), ("phenomenon", "non-maximality")] }

def ex_27 : Datum :=
  { id := "tieukrizchemla2019_27"
    source := ⟨"tieu-kriz-chemla-2019", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Oh my, we have to go back — the windows are open!"
    glossedTokens := []
    context := "Mary has a house with over a dozen windows and forgot to close just a few of them; Max asks whether the house will be all right in the coming thunderstorm."
    judgment := .acceptable
    contrasts := []
    readings := [("non-maximal, effectively existential", .acceptable)]
    paperFeatures := [("determiner", "the"), ("polarity", "positive"), ("phenomenon", "non-maximality")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_8a, ex_8b, ex_9a, ex_9b, ex_12a, ex_12b, ex_13a, ex_13b, ex_14a, ex_14b, si_target, ex_26, ex_27]

end TieuKrizChemla2019.Examples
