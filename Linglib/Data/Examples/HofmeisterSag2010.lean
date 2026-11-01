module

public import Linglib.Data.Examples.Schema

/-!
# `HofmeisterSag2010` — typed example data

Auto-generated from `Linglib/Data/Examples/HofmeisterSag2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HofmeisterSag2010.Examples`.
-/

@[expose] public section

namespace HofmeisterSag2010.Examples

def ex42a : Datum :=
  { id := "hofmeistersag2010_ex42a"
    source := ⟨"hofmeister-sag-2010", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which man saw the girl in the bar on California Avenue?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("factor", "locality"), ("dependency", "subject")] }

def ex42b : Datum :=
  { id := "hofmeistersag2010_ex42b"
    source := ⟨"hofmeister-sag-2010", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which man did the girl in the bar on California Avenue see?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("factor", "locality"), ("dependency", "object")] }

def ex43 : Datum :=
  { id := "hofmeistersag2010_ex43"
    source := ⟨"hofmeister-sag-2010", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The consultant who (we/Donald Trump/the chairman/a chairman) called advised wealthy companies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("factor", "referential load")] }

def ex44a : Datum :=
  { id := "hofmeistersag2010_ex44a"
    source := ⟨"hofmeister-sag-2010", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has she forgotten that he dragged her to a movie on Christmas Eve?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("factor", "clause boundary"), ("complementizer", "that")] }

def ex44b : Datum :=
  { id := "hofmeistersag2010_ex44b"
    source := ⟨"hofmeister-sag-2010", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has she forgotten if he dragged her to a movie on Christmas Eve?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("factor", "clause boundary"), ("complementizer", "if")] }

def ex44c : Datum :=
  { id := "hofmeistersag2010_ex44c"
    source := ⟨"hofmeister-sag-2010", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has she forgotten who he dragged to a movie on Christmas Eve?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("factor", "clause boundary"), ("complementizer", "who")] }

def ex45a : Datum :=
  { id := "hofmeistersag2010_ex45a"
    source := ⟨"hofmeister-sag-2010", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The diplomat contacted the dictator who the activist looking for more contributions encouraged to preserve natural habitats and resources."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("factor", "filler complexity"), ("filler", "simple")] }

def ex45b : Datum :=
  { id := "hofmeistersag2010_ex45b"
    source := ⟨"hofmeister-sag-2010", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The diplomat contacted the ruthless military dictator who the activist looking for more contributions encouraged to preserve natural habitats and resources."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("factor", "filler complexity"), ("filler", "complex")] }

def ex46 : Datum :=
  { id := "hofmeistersag2010_ex46"
    source := ⟨"hofmeister-sag-2010", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which politician did you read reports that we had impeached?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5"), ("island", "complexNP")] }

def ex48_bareDef : Datum :=
  { id := "hofmeistersag2010_ex48_bareDef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "I saw who Emma doubted the report that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "bare"), ("islandNP", "definite")] }

def ex48_barePl : Datum :=
  { id := "hofmeistersag2010_ex48_barePl"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "I saw who Emma doubted reports that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "bare"), ("islandNP", "plural")] }

def ex48_bareIndef : Datum :=
  { id := "hofmeistersag2010_ex48_bareIndef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "I saw who Emma doubted a report that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "bare"), ("islandNP", "indefinite")] }

def ex48_whichDef : Datum :=
  { id := "hofmeistersag2010_ex48_whichDef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted the report that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "whichN"), ("islandNP", "definite")] }

def ex48_whichPl : Datum :=
  { id := "hofmeistersag2010_ex48_whichPl"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted reports that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "whichN"), ("islandNP", "plural")] }

def ex48_whichIndef : Datum :=
  { id := "hofmeistersag2010_ex48_whichIndef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted a report that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "whichN"), ("islandNP", "indefinite")] }

def ex48_baseline : Datum :=
  { id := "hofmeistersag2010_ex48_baseline"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted that we had captured in the nationwide FBI manhunt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "none"), ("filler", "whichN")] }

def ex49_bare : Datum :=
  { id := "hofmeistersag2010_ex49_bare"
    source := ⟨"hofmeister-sag-2010", "(49)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Who did Albert learn whether they dismissed after the annual performance review?"
    glossedTokens := []
    context := "Albert learned that the managers dismissed the employee with poor sales after the annual performance review."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("experiment", "2"), ("island", "embeddedQuestion"), ("filler", "bare")] }

def ex49_which : Datum :=
  { id := "hofmeistersag2010_ex49_which"
    source := ⟨"hofmeister-sag-2010", "(49)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Which employee did Albert learn whether they dismissed after the annual performance review?"
    glossedTokens := []
    context := "Albert learned that the managers dismissed the employee with poor sales after the annual performance review."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("experiment", "2"), ("island", "embeddedQuestion"), ("filler", "whichN")] }

def ex49_baseline : Datum :=
  { id := "hofmeistersag2010_ex49_baseline"
    source := ⟨"hofmeister-sag-2010", "(49)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Who did Albert learn that they dismissed after the annual performance review?"
    glossedTokens := []
    context := "Albert learned that the managers dismissed the employee with poor sales after the annual performance review."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("experiment", "2"), ("island", "none"), ("filler", "bare")] }

def all : List Datum := [ex42a, ex42b, ex43, ex44a, ex44b, ex44c, ex45a, ex45b, ex46, ex48_bareDef, ex48_barePl, ex48_bareIndef, ex48_whichDef, ex48_whichPl, ex48_whichIndef, ex48_baseline, ex49_bare, ex49_which, ex49_baseline]

end HofmeisterSag2010.Examples
