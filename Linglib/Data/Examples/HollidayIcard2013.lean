module

public import Linglib.Data.Examples.Schema

/-!
# `HollidayIcard2013` — typed example data

Auto-generated from `Linglib/Data/Examples/HollidayIcard2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HollidayIcard2013.Examples`.
-/

@[expose] public section

namespace HollidayIcard2013.Examples

def ex1 : Datum :=
  { id := "hollidayicard2013_ex1"
    source := ⟨"holliday-icard-2013", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is at least as likely that one of Brazil or Qatar will win the World Cup as it is that one of the U.S. or Qatar will win the World Cup."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("axiom", "A"), ("form", "(φ ∨ χ) ⩾ (ψ ∨ χ)")] }

def ex2 : Datum :=
  { id := "hollidayicard2013_ex2"
    source := ⟨"holliday-icard-2013", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is at least as likely that Brazil will win the World Cup as it is that the U.S. will win the World Cup."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("axiom", "A"), ("form", "φ ⩾ ψ")] }

def ex3 : Datum :=
  { id := "hollidayicard2013_ex3"
    source := ⟨"holliday-icard-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that one of Argentina or England will win the World Cup than it is that one of China or Denmark will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{a, e} ≻ {c, d}")] }

def ex4 : Datum :=
  { id := "hollidayicard2013_ex4"
    source := ⟨"holliday-icard-2013", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that one of Brazil or China will win than it is that one of Argentina or Denmark will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{b, c} ≻ {a, d}")] }

def ex5 : Datum :=
  { id := "hollidayicard2013_ex5"
    source := ⟨"holliday-icard-2013", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that Denmark will win than it is that one of Argentina or China will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{d} ≻ {a, c}")] }

def ex6 : Datum :=
  { id := "hollidayicard2013_ex6"
    source := ⟨"holliday-icard-2013", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that one of Argentina, China, or Denmark will win than it is that one of Brazil or England will win."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{a, c, d} ≻ {b, e}")] }

def all : List Datum := [ex1, ex2, ex3, ex4, ex5, ex6]

end HollidayIcard2013.Examples
