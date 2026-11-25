module

public import Linglib.Data.Examples.Schema

/-!
# `Buring2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Buring2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Buring2007.Examples`.
-/

@[expose] public section

namespace Buring2007.Examples

def ex_1a : Datum :=
  { id := "buring2007_1a"
    source := ⟨"buring-2007", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is shorter than Mary is tall."
    glossedTokens := []
    context := ""
    judgment := .nearlyUngrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "buring2007_1b"
    source := ⟨"buring-2007", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is taller than John is short."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "buring2007_2a"
    source := ⟨"buring-2007", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the ladder was shorter than the house was high."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2b : Datum :=
  { id := "buring2007_2b"
    source := ⟨"buring-2007", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My yacht is shorter than yours is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2c : Datum :=
  { id := "buring2007_2c"
    source := ⟨"buring-2007", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your dinghy should be shorter than your boat is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_3 : Datum :=
  { id := "buring2007_3"
    source := ⟨"buring-2007", "(3)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Funiculus narrowing medially, segments 3–5 narrower than long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_4 : Datum :=
  { id := "buring2007_4"
    source := ⟨"buring-2007", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the hose is shorter than the ladder is long."
    glossedTokens := []
    context := ""
    judgment := .nearlyUngrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_5 : Datum :=
  { id := "buring2007_5"
    source := ⟨"buring-2007", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the house is higher than the ladder is short."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10 : Datum :=
  { id := "buring2007_10"
    source := ⟨"buring-2007", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the ladder was shorter than the house was."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_26 : Datum :=
  { id := "buring2007_26"
    source := ⟨"buring-2007", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You rope is more than mine is long."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_29 : Datum :=
  { id := "buring2007_29"
    source := ⟨"buring-2007", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the existing drawbridge is shorter than the new moat has to be wide."
    glossedTokens := []
    context := "A regulation requires the moat to be at least 30 feet wide; the existing drawbridge is 15 feet long."
    judgment := .acceptable
    contrasts := []
    readings := [("the minimum required width of the moat is more than the length of the drawbridge", .acceptable), ("the maximum allowed width of the moat is more than the length of the drawbridge", .ungrammatical)]
    paperFeatures := [] }

def ex_34 : Datum :=
  { id := "buring2007_34"
    source := ⟨"buring-2007", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The new drawbridge is less wide than the coaches have to be."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("the coaches have to be wider than the drawbridge is", .acceptable)]
    paperFeatures := [] }

def ex_35 : Datum :=
  { id := "buring2007_35"
    source := ⟨"buring-2007", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The new drawbridge is narrower than the coaches have to be."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("the coaches can be wider than the drawbridge is", .acceptable)]
    paperFeatures := [] }

def ex_38 : Datum :=
  { id := "buring2007_38"
    source := ⟨"buring-2007", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The moat around our new castle is narrower than drawbridges are allowed to be long around here."
    glossedTokens := []
    context := "The speaker feared that local codes allow no drawbridge long enough to span the moat."
    judgment := .acceptable
    contrasts := []
    readings := [("the width of the moat is less than the maximum permitted length of drawbridges", .acceptable), ("the width of the moat is less than the minimum permitted length of drawbridges", .ungrammatical)]
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_2c, ex_3, ex_4, ex_5, ex_10, ex_26, ex_29, ex_34, ex_35, ex_38]

end Buring2007.Examples
