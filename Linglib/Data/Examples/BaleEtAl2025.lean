module

public import Linglib.Data.Examples.Schema

/-!
# `BaleEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/BaleEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BaleEtAl2025.Examples`.
-/

@[expose] public section

namespace BaleEtAl2025.Examples

def ex_1 : Datum :=
  { id := "baleetal2025_1"
    source := ⟨"bale-etal-2025", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sarah solved some of the math problems."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "some")] }

def ex_2 : Datum :=
  { id := "baleetal2025_2"
    source := ⟨"bale-etal-2025", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sarah solved all of the math problems."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "all")] }

def fk_all : Datum :=
  { id := "baleetal2025_fk_all"
    source := ⟨"bale-etal-2025", "Full-Knowledge+All trial"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the boxes have red cubes."
    glossedTokens := []
    context := "Farmer Brown opened boxes 1 and 2, each visibly containing two red foam cubes, and looked into box 3, whose contents the participant cannot see; asked whether Farmer Brown knows what is in box 3, the participant answered yes. Asked afterwards: Do you think there are red cubes in this box (box 3)?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "all"), ("boxesSeen", "3"), ("expectedResponse", "yes")] }

def fk_some : Datum :=
  { id := "baleetal2025_fk_some"
    source := ⟨"bale-etal-2025", "Full-Knowledge+Some trial"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Some of the boxes have red cubes."
    glossedTokens := []
    context := "Farmer Brown opened boxes 1 and 2, each visibly containing two red foam cubes, and looked into box 3, whose contents the participant cannot see; asked whether Farmer Brown knows what is in box 3, the participant answered yes. Asked afterwards: Do you think there are red cubes in this box (box 3)?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "some"), ("boxesSeen", "3"), ("expectedResponse", "no")] }

def pk_some : Datum :=
  { id := "baleetal2025_pk_some"
    source := ⟨"bale-etal-2025", "Partial-Knowledge+Some trial (4)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Some of the boxes have red cubes."
    glossedTokens := []
    context := "Farmer Brown opened boxes 1 and 2, each visibly containing two red foam cubes, and did not look into box 3, whose contents the participant cannot see; asked whether Farmer Brown knows what is in box 3, the participant answered no. Asked afterwards: Do you think there are red cubes in this box (box 3)?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "some"), ("boxesSeen", "2"), ("expectedResponse", "dontKnow")] }

def all : List Datum := [ex_1, ex_2, fk_all, fk_some, pk_some]

end BaleEtAl2025.Examples
