module

public import Linglib.Data.Examples.Schema

/-!
# `Anderson2006b` — typed example data

Auto-generated from `Linglib/Data/Examples/Anderson2006b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anderson2006b.Examples`.
-/

@[expose] public section

namespace Anderson2006b.Examples

def ex_3 : Datum :=
  { id := "anderson2006b_3"
    source := ⟨"anderson-2006b", "ch. 6 (3)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il va/est à Toulouse"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("neutralized", "loc{goal}"), ("neutralized", "loc")] }

def ex_39a : Datum :=
  { id := "anderson2006b_39a"
    source := ⟨"anderson-2006b", "ch. 6 (39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill read the book"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "erg"), ("arg", "abs"), ("subject", "erg")] }

def ex_39b : Datum :=
  { id := "anderson2006b_39b"
    source := ⟨"anderson-2006b", "ch. 6 (39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill fell to the ground"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "abs"), ("arg", "loc{goal}"), ("subject", "abs")] }

def ex_39c : Datum :=
  { id := "anderson2006b_39c"
    source := ⟨"anderson-2006b", "ch. 6 (39c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill flew to China"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "abs,erg"), ("arg", "loc{goal}"), ("subject", "abs,erg")] }

def ex_39h : Datum :=
  { id := "anderson2006b_39h"
    source := ⟨"anderson-2006b", "ch. 6 (39h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill knew the answer"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "erg,loc"), ("arg", "abs"), ("subject", "erg,loc")] }

def ex_39i : Datum :=
  { id := "anderson2006b_39i"
    source := ⟨"anderson-2006b", "ch. 6 (39i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill acquired a new shirt"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "erg,loc{goal}"), ("arg", "abs"), ("subject", "erg,loc{goal}")] }

def ex_39j : Datum :=
  { id := "anderson2006b_39j"
    source := ⟨"anderson-2006b", "ch. 6 (39j)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill suffered from asthma"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "abs,erg,loc{goal}"), ("arg", "loc{src}"), ("subject", "abs,erg,loc{goal}")] }

def ex_34 : Datum :=
  { id := "anderson2006b_34"
    source := ⟨"anderson-2006b", "ch. 6 (34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Phil suffered (from asthma)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "abs,erg,loc{goal}"), ("arg", "loc{src}"), ("subject", "abs,erg,loc{goal}")] }

def ex_4_8a : Datum :=
  { id := "anderson2006b_4_8a"
    source := ⟨"anderson-2006b", "ch. 6 (4.8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sewage flooded into the tank"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "abs"), ("arg", "loc"), ("subject", "abs")] }

def ex_4_8b : Datum :=
  { id := "anderson2006b_4_8b"
    source := ⟨"anderson-2006b", "ch. 6 (4.8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tank flooded with sewage"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "abs,loc"), ("adjunct", "abs"), ("subject", "abs,loc")] }

def ex_23a : Datum :=
  { id := "anderson2006b_23a"
    source := ⟨"anderson-2006b", "ch. 6 (23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill reads lots of books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("arg", "erg"), ("arg", "abs"), ("subject", "erg")] }

def all : List Datum := [ex_3, ex_39a, ex_39b, ex_39c, ex_39h, ex_39i, ex_39j, ex_34, ex_4_8a, ex_4_8b, ex_23a]

end Anderson2006b.Examples
