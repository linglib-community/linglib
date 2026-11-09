module

public import Linglib.Data.Examples.Schema

/-!
# `Barker2027` — typed example data

Auto-generated from `Linglib/Data/Examples/Barker2027.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Barker2027.Examples`.
-/

@[expose] public section

namespace Barker2027.Examples

def ex_18a : Datum :=
  { id := "barker2027_18a"
    source := ⟨"barker-2027", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone asked everyone to leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .acceptable)]
    paperFeatures := [] }

def ex_18b : Datum :=
  { id := "barker2027_18b"
    source := ⟨"barker-2027", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone thought everyone left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .unacceptable)]
    paperFeatures := [] }

def ex_19a : Datum :=
  { id := "barker2027_19a"
    source := ⟨"barker-2027", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a bone in every corner of the house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .acceptable)]
    paperFeatures := [] }

def ex_19b : Datum :=
  { id := "barker2027_19b"
    source := ⟨"barker-2027", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a bone that is in every corner of the house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .unacceptable)]
    paperFeatures := [] }

def ex_20a : Datum :=
  { id := "barker2027_20a"
    source := ⟨"barker-2027", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone needs to clean the room after each guest has left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .acceptable)]
    paperFeatures := [] }

def ex_20b : Datum :=
  { id := "barker2027_20b"
    source := ⟨"barker-2027", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A student made sure that each speaker had a ride."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b]

end Barker2027.Examples
