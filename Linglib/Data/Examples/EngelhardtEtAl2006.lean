module

public import Linglib.Data.Examples.Schema

/-!
# `EngelhardtEtAl2006` — typed example data

Auto-generated from `Linglib/Data/Examples/EngelhardtEtAl2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace EngelhardtEtAl2006.Examples`.
-/

@[expose] public section

namespace EngelhardtEtAl2006.Examples

def ex_1 : Datum :=
  { id := "engelhardtetal2006_1"
    source := ⟨"engelhardt-etal-2006", "(1)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple on the towel in the box."
    glossedTokens := []
    context := "An apple on a towel, a distractor of another kind, an empty towel and an empty box (Fig. 1A)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ambiguity", "ambiguous")] }

def ex_2 : Datum :=
  { id := "engelhardtetal2006_2"
    source := ⟨"engelhardt-etal-2006", "(2)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple that's on the towel in the box."
    glossedTokens := []
    context := "An apple on a towel, a distractor of another kind, an empty towel and an empty box (Fig. 1A)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ambiguity", "unambiguous")] }

def ex_3 : Datum :=
  { id := "engelhardtetal2006_3"
    source := ⟨"engelhardt-etal-2006", "Table 1, (3)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple on the towel."
    glossedTokens := []
    context := "The apple is on a towel and is to be moved to the other towel."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "bare"), ("destination", "towel")] }

def ex_4 : Datum :=
  { id := "engelhardtetal2006_4"
    source := ⟨"engelhardt-etal-2006", "Table 1, (4)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple in the box."
    glossedTokens := []
    context := "The apple is on a towel and is to be moved to the box."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "bare"), ("destination", "box")] }

def ex_5 : Datum :=
  { id := "engelhardtetal2006_5"
    source := ⟨"engelhardt-etal-2006", "Table 1, (5)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple on the towel on the other towel."
    glossedTokens := []
    context := "The apple is on a towel and is to be moved to the other towel."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "modified"), ("destination", "otherTowel")] }

def ex_6 : Datum :=
  { id := "engelhardtetal2006_6"
    source := ⟨"engelhardt-etal-2006", "Table 1, (6)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple on the towel in the box."
    glossedTokens := []
    context := "The apple is on a towel and is to be moved to the box."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "modified"), ("destination", "box")] }

def ex_7 : Datum :=
  { id := "engelhardtetal2006_7"
    source := ⟨"engelhardt-etal-2006", "(7)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Put the apple in the box on the towel."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end EngelhardtEtAl2006.Examples
