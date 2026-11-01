module

public import Linglib.Data.Examples.Schema

/-!
# `HeKaiserIskarous2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HeKaiserIskarous2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HeKaiserIskarous2025.Examples`.
-/

@[expose] public section

namespace HeKaiserIskarous2025.Examples

def house_no_bathroom : Datum :=
  { id := "hekaiseriskarous2025_house_no_bathroom"
    source := ⟨"he-kaiser-iskarous-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house doesn't have a bathroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("polarity", "negative"), ("statePrior", "low")] }

def house_ballroom : Datum :=
  { id := "hekaiseriskarous2025_house_ballroom"
    source := ⟨"he-kaiser-iskarous-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house has a ballroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("polarity", "positive"), ("statePrior", "low")] }

def house_no_ballroom : Datum :=
  { id := "hekaiseriskarous2025_house_no_ballroom"
    source := ⟨"he-kaiser-iskarous-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The house doesn't have a ballroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("polarity", "negative"), ("statePrior", "high")] }

def exp1_pos : Datum :=
  { id := "hekaiseriskarous2025_exp1_pos"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "The house has a bathroom."
    glossedTokens := []
    context := "Emma visited a friend's house yesterday."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "positive"), ("experiment", "1")] }

def exp1_neg : Datum :=
  { id := "hekaiseriskarous2025_exp1_neg"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "The house doesn't have a bathroom."
    glossedTokens := []
    context := "Emma visited a friend's house yesterday."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "negative"), ("experiment", "1")] }

def classroom_no_board : Datum :=
  { id := "hekaiseriskarous2025_classroom_no_board"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The classroom doesn't have a board."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "negative"), ("statePrior", "low")] }

def classroom_stove : Datum :=
  { id := "hekaiseriskarous2025_classroom_stove"
    source := ⟨"he-kaiser-iskarous-2025", "§3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The classroom has a stove."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("polarity", "positive"), ("statePrior", "low")] }

def exp2 : Datum :=
  { id := "hekaiseriskarous2025_exp2"
    source := ⟨"he-kaiser-iskarous-2025", "§3.3"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "“The house has a bathroom,” Emma told her partner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("polarity", "positive"), ("experiment", "2")] }

def all : List Datum := [house_no_bathroom, house_ballroom, house_no_ballroom, exp1_pos, exp1_neg, classroom_no_board, classroom_stove, exp2]

end HeKaiserIskarous2025.Examples
