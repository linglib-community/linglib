module

public import Linglib.Data.Examples.Schema

/-!
# `Adams1975` — typed example data

Auto-generated from `Linglib/Data/Examples/Adams1975.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Adams1975.Examples`.
-/

@[expose] public section

namespace Adams1975.Examples

def p15 : Datum :=
  { id := "adams1975_p15"
    source := ⟨"adams-1975", "p. 15"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it rains tomorrow there will not be a terrific cloudburst. If there is a terrific cloudburst tomorrow it will not rain."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "contraposition")] }

def p16a : Datum :=
  { id := "adams1975_p16a"
    source := ⟨"adams-1975", "p. 16"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either it will rain or it will snow in Berkeley next year. If it doesn't rain then it will snow in Berkeley next year."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "disjunction")] }

def p16b : Datum :=
  { id := "adams1975_p16b"
    source := ⟨"adams-1975", "p. 16"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Smith dies before the election Jones will win. If Jones wins then Smith will retire. If Smith dies before the election he will retire."
    glossedTokens := []
    context := "Smith and Jones are the only candidates for a public office of which Smith is the incumbent, and Smith has announced his intention of retiring to private life in the event of his defeat."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "hypotheticalSyllogism")] }

def p17 : Datum :=
  { id := "adams1975_p17"
    source := ⟨"adams-1975", "p. 17"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Jones wins the election then Smith will retire. If Smith dies before the election and Jones wins then Smith will retire."
    glossedTokens := []
    context := "Smith and Jones are the only candidates for a public office of which Smith is the incumbent, and Smith has announced his intention of retiring to private life in the event of his defeat."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("pattern", "antecedentRestriction")] }

def all : List Datum := [p15, p16a, p16b, p17]

end Adams1975.Examples
