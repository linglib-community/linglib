module

public import Linglib.Data.Examples.Schema

/-!
# `Kratzer1981` — typed example data

Auto-generated from `Linglib/Data/Examples/Kratzer1981.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kratzer1981.Examples`.
-/

@[expose] public section

namespace Kratzer1981.Examples

def first : Datum :=
  { id := "kratzer1981_first"
    source := ⟨"kratzer-1981", "p. 65"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Considering the relevant circumstances and what I want, it is necessary in w that I go to the pub regularly."
    glossedTokens := []
    context := "In w, all I want is to become mayor. In w, the relevant circumstances are such that I will become mayor only if I go to the pub regularly."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def one : Datum :=
  { id := "kratzer1981_one"
    source := ⟨"kratzer-1981", "p. 66, conclusion one"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Considering the relevant circumstances and what I want, it is necessary in w that I go to the pub regularly."
    glossedTokens := []
    context := "In w, all I want is two things, namely to become mayor and not to go to the pub regularly. In w the relevant circumstances are such that I will become mayor only if I go to the pub regularly."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def two : Datum :=
  { id := "kratzer1981_two"
    source := ⟨"kratzer-1981", "p. 66, conclusion two"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Considering the relevant circumstances and what I want, it is necessary in w that I don't go to the pub regularly."
    glossedTokens := []
    context := "In w, all I want is two things, namely to become mayor and not to go to the pub regularly. In w the relevant circumstances are such that I will become mayor only if I go to the pub regularly."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def three : Datum :=
  { id := "kratzer1981_three"
    source := ⟨"kratzer-1981", "p. 66, conclusion three"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Considering the relevant circumstances and what I want, it is possible in w that I don't go to the pub regularly and still will become mayor."
    glossedTokens := []
    context := "In w, all I want is two things, namely to become mayor and not to go to the pub regularly. In w the relevant circumstances are such that I will become mayor only if I go to the pub regularly."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def four : Datum :=
  { id := "kratzer1981_four"
    source := ⟨"kratzer-1981", "p. 66, conclusion four"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Considering the relevant circumstances and what I want, it is possible in w that I go to the pub regularly."
    glossedTokens := []
    context := "In w, all I want is two things, namely to become mayor and not to go to the pub regularly. In w the relevant circumstances are such that I will become mayor only if I go to the pub regularly."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def five : Datum :=
  { id := "kratzer1981_five"
    source := ⟨"kratzer-1981", "p. 66, conclusion five"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Considering the relevant circumstances and what I want, it is possible in w that I don't go to the pub regularly."
    glossedTokens := []
    context := "In w, all I want is two things, namely to become mayor and not to go to the pub regularly. In w the relevant circumstances are such that I will become mayor only if I go to the pub regularly."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_75 : Datum :=
  { id := "kratzer1981_75"
    source := ⟨"kratzer-1981", "p. 70 (75)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jedem Menschen muß Gerechtigkeit widerfahren."
    glossedTokens := []
    context := "The modal base is empty and the ordering source is what is morally commanded."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_76 : Datum :=
  { id := "kratzer1981_76"
    source := ⟨"kratzer-1981", "p. 70 (76)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wenn jemand ungerecht behandelt wurde, muß das Unrecht wieder gutgemacht werden."
    glossedTokens := []
    context := "The modal base is empty and the ordering source is what is morally commanded."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_77 : Datum :=
  { id := "kratzer1981_77"
    source := ⟨"kratzer-1981", "p. 70 (77)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wenn jemand ungerecht behandelt wurde, muß er mundtot gemacht werden."
    glossedTokens := []
    context := "The modal base is empty and the ordering source is what is morally commanded."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [first, one, two, three, four, five, ex_75, ex_76, ex_77]

end Kratzer1981.Examples
