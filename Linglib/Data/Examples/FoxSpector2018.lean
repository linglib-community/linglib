module

public import Linglib.Data.Examples.Schema

/-!
# `FoxSpector2018` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxSpector2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxSpector2018.Examples`.
-/

@[expose] public section

namespace FoxSpector2018.Examples

def ex14a : Datum :=
  { id := "foxspector2018_ex14a"
    source := ⟨"hurford-1974", "Hurford's Constraint"⟩
    reportedIn := some ⟨"fox-spector-2018", "(14a)"⟩
    language := "stan1293"
    primaryText := "John was born in France or Paris."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "no"), ("order", "canonical"), ("distant", "no"), ("de", "0")] }

def ex14b : Datum :=
  { id := "foxspector2018_ex14b"
    source := ⟨"fox-spector-2018", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have a dog or a German Shepherd."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "no"), ("order", "canonical"), ("distant", "no"), ("de", "0")] }

def ex16a : Datum :=
  { id := "foxspector2018_ex16a"
    source := ⟨"hurford-1974", "(16a)"⟩
    reportedIn := some ⟨"fox-spector-2018", "(16a)"⟩
    language := "stan1293"
    primaryText := "John talked to Mary or Sue or both."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "0")] }

def ex16b : Datum :=
  { id := "foxspector2018_ex16b"
    source := ⟨"fox-spector-2018", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some or all of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "0")] }

def ex16c : Datum :=
  { id := "foxspector2018_ex16c"
    source := ⟨"gazdar-1979", "(16c)"⟩
    reportedIn := some ⟨"fox-spector-2018", "(16c)"⟩
    language := "stan1293"
    primaryText := "John read three books or more."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "0")] }

def ex18a : Datum :=
  { id := "foxspector2018_ex18a"
    source := ⟨"fox-spector-2018", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has three or six children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "yes"), ("de", "0")] }

def ex18b : Datum :=
  { id := "foxspector2018_ex18b"
    source := ⟨"fox-spector-2018", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The water is (somewhat) warm or absolutely boiling."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "yes"), ("de", "0")] }

def ex12b : Datum :=
  { id := "foxspector2018_ex12b"
    source := ⟨"singh-2008", "Singh's Asymmetry"⟩
    reportedIn := some ⟨"fox-spector-2018", "(12b)"⟩
    language := "stan1293"
    primaryText := "John talked to both Mary and Sue, or to Mary or Sue."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "reverse"), ("distant", "no"), ("de", "0")] }

def ex46 : Datum :=
  { id := "foxspector2018_ex46"
    source := ⟨"fox-spector-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The water is absolutely boiling or (somewhat) warm."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "reverse"), ("distant", "yes"), ("de", "0")] }

def ex10a : Datum :=
  { id := "foxspector2018_ex10a"
    source := ⟨"gajewski-sharvit-2012", "Hurford under negation"⟩
    reportedIn := some ⟨"fox-spector-2018", "(10a)"⟩
    language := "stan1293"
    primaryText := "John didn't talk to Mary or Sue, or both."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "1")] }

def ex65a : Datum :=
  { id := "foxspector2018_ex65a"
    source := ⟨"fox-spector-2018", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't hand in the first or second assignment or both."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "1")] }

def ex65b : Datum :=
  { id := "foxspector2018_ex65b"
    source := ⟨"fox-spector-2018", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who didn't hand in the first or second assignment or both failed the class."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "2")] }

def ex66a : Datum :=
  { id := "foxspector2018_ex66a"
    source := ⟨"fox-spector-2018", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I would go to the movies without John or Bill or both."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "1")] }

def ex66b : Datum :=
  { id := "foxspector2018_ex66b"
    source := ⟨"fox-spector-2018", "(66b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wouldn't go to the movies without John or Bill or both."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hurford", "yes"), ("rescuable", "yes"), ("order", "canonical"), ("distant", "no"), ("de", "2")] }

def all : List Datum := [ex14a, ex14b, ex16a, ex16b, ex16c, ex18a, ex18b, ex12b, ex46, ex10a, ex65a, ex65b, ex66a, ex66b]

end FoxSpector2018.Examples
