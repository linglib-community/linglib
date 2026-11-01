module

public import Linglib.Data.Examples.Schema

/-!
# `Chomsky1981` — typed example data

Auto-generated from `Linglib/Data/Examples/Chomsky1981.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chomsky1981.Examples`.
-/

@[expose] public section

namespace Chomsky1981.Examples

def ex_92i : Datum :=
  { id := "chomsky1981_92i"
    source := ⟨"chomsky-1981", "(92i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw my picture of him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_92ii : Datum :=
  { id := "chomsky1981_92ii"
    source := ⟨"chomsky-1981", "(92ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's picture of him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_92iii : Datum :=
  { id := "chomsky1981_92iii"
    source := ⟨"chomsky-1981", "(92iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw a picture of him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_92iv : Datum :=
  { id := "chomsky1981_92iv"
    source := ⟨"chomsky-1981", "(92iv)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought I saw a picture of him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_92v : Datum :=
  { id := "chomsky1981_92v"
    source := ⟨"chomsky-1981", "(92v)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John read his book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_92vi : Datum :=
  { id := "chomsky1981_92vi"
    source := ⟨"chomsky-1981", "(92vi)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought I saw his book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_93 : Datum :=
  { id := "chomsky1981_93"
    source := ⟨"chomsky-1981", "(93)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They read each other's books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_78_my : Datum :=
  { id := "chomsky1981_78_my"
    source := ⟨"chomsky-1981", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They heard my stories about each other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_78_the : Datum :=
  { id := "chomsky1981_78_the"
    source := ⟨"chomsky-1981", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They heard the stories about each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_78_none : Datum :=
  { id := "chomsky1981_78_none"
    source := ⟨"chomsky-1981", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They heard stories about each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_79i : Datum :=
  { id := "chomsky1981_79i"
    source := ⟨"chomsky-1981", "(79i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They expected me to hear stories about each other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_79ii : Datum :=
  { id := "chomsky1981_79ii"
    source := ⟨"chomsky-1981", "(79ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They expected that pictures of each other would be on sale."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_80 : Datum :=
  { id := "chomsky1981_80"
    source := ⟨"chomsky-1981", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They thought I expected that pictures of each other would be on sale."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_92i, ex_92ii, ex_92iii, ex_92iv, ex_92v, ex_92vi, ex_93, ex_78_my, ex_78_the, ex_78_none, ex_79i, ex_79ii, ex_80]

end Chomsky1981.Examples
