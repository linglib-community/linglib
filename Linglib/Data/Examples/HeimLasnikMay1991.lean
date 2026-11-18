module

public import Linglib.Data.Examples.Schema

/-!
# `HeimLasnikMay1991` — typed example data

Auto-generated from `Linglib/Data/Examples/HeimLasnikMay1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HeimLasnikMay1991.Examples`.
-/

@[expose] public section

namespace HeimLasnikMay1991.Examples

def ex1 : Datum :=
  { id := "heimlasnikmay1991_ex1"
    source := ⟨"heim-lasnik-may-1991", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The spies suspected each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1")] }

def ex2 : Datum :=
  { id := "heimlasnikmay1991_ex2"
    source := ⟨"heim-lasnik-may-1991", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary told each other that they should leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("readings", "I; you; we")] }

def ex4 : Datum :=
  { id := "heimlasnikmay1991_ex4"
    source := ⟨"heim-lasnik-may-1991", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary think they like each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("readings", "narrow; broad")] }

def ex5 : Datum :=
  { id := "heimlasnikmay1991_ex5"
    source := ⟨"heim-lasnik-may-1991", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of John and Mary thinks that s/he likes the other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "broad")] }

def ex6 : Datum :=
  { id := "heimlasnikmay1991_ex6"
    source := ⟨"heim-lasnik-may-1991", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary think that I like each other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "1")] }

def ex7 : Datum :=
  { id := "heimlasnikmay1991_ex7"
    source := ⟨"heim-lasnik-may-1991", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men saw each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("lf", "[[the men]₁ each₂] saw [e₂ other]₃")] }

def ex24 : Datum :=
  { id := "heimlasnikmay1991_ex24"
    source := ⟨"heim-lasnik-may-1991", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They cramped each other's style."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.3")] }

def ex27 : Datum :=
  { id := "heimlasnikmay1991_ex27"
    source := ⟨"heim-lasnik-may-1991", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men each left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("distributor", "floated each")] }

def ex30 : Datum :=
  { id := "heimlasnikmay1991_ex30"
    source := ⟨"heim-lasnik-may-1991", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary argue that they will win $100."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("readings", "we; each")] }

def ex36 : Datum :=
  { id := "heimlasnikmay1991_ex36"
    source := ⟨"heim-lasnik-may-1991", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary and Sally introduced themselves to each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("reading", "distributive only")] }

def ex38 : Datum :=
  { id := "heimlasnikmay1991_ex38"
    source := ⟨"heim-lasnik-may-1991", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary and Sally each introduced themselves to the other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4")] }

def ex39b : Datum :=
  { id := "heimlasnikmay1991_ex39b"
    source := ⟨"heim-lasnik-may-1991", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of the women introduced themselves to the other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4")] }

def ex40a : Datum :=
  { id := "heimlasnikmay1991_ex40a"
    source := ⟨"heim-lasnik-may-1991", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The women convinced each other that they should leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4")] }

def ex42a : Datum :=
  { id := "heimlasnikmay1991_ex42a"
    source := ⟨"heim-lasnik-may-1991", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The doctors each gave the other a new nose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4")] }

def ex43 : Datum :=
  { id := "heimlasnikmay1991_ex43"
    source := ⟨"heim-lasnik-may-1991", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary told each other that they should leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("readings", "I; you; we together; we separately")] }

def ex45 : Datum :=
  { id := "heimlasnikmay1991_ex45"
    source := ⟨"heim-lasnik-may-1991", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary persuaded each other to leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("reading", "you")] }

def ex46 : Datum :=
  { id := "heimlasnikmay1991_ex46"
    source := ⟨"heim-lasnik-may-1991", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary promised each other to leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("reading", "I")] }

def ex57 : Datum :=
  { id := "heimlasnikmay1991_ex57"
    source := ⟨"heim-lasnik-may-1991", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The candidates criticized each other after they had left the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("readings", "I; you; we")] }

def ex60 : Datum :=
  { id := "heimlasnikmay1991_ex60"
    source := ⟨"heim-lasnik-may-1991", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "After they had left the room, the candidates criticized each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("readings", "we")] }

def ex61a : Datum :=
  { id := "heimlasnikmay1991_ex61a"
    source := ⟨"heim-lasnik-may-1991", "(61a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They criticized every candidate after he had left the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1")] }

def ex64 : Datum :=
  { id := "heimlasnikmay1991_ex64"
    source := ⟨"heim-lasnik-may-1991", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary think that they like each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("readings", "narrow (65); broad (66)")] }

def ex68 : Datum :=
  { id := "heimlasnikmay1991_ex68"
    source := ⟨"heim-lasnik-may-1991", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are taller than each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("reading", "contradictory")] }

def ex69 : Datum :=
  { id := "heimlasnikmay1991_ex69"
    source := ⟨"heim-lasnik-may-1991", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They think they are taller than each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("readings", "noncontradictory broad; contradictory narrow")] }

def ex71 : Datum :=
  { id := "heimlasnikmay1991_ex71"
    source := ⟨"heim-lasnik-may-1991", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They each think they are taller than each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("reading", "contradictory narrow only")] }

def ex72 : Datum :=
  { id := "heimlasnikmay1991_ex72"
    source := ⟨"heim-lasnik-may-1991", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They each examined each other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4")] }

def ex73 : Datum :=
  { id := "heimlasnikmay1991_ex73"
    source := ⟨"heim-lasnik-may-1991", "(73)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They think they each are taller than each other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4")] }

def ex77 : Datum :=
  { id := "heimlasnikmay1991_ex77"
    source := ⟨"heim-lasnik-may-1991", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They each think they are sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1")] }

def all : List Datum := [ex1, ex2, ex4, ex5, ex6, ex7, ex24, ex27, ex30, ex36, ex38, ex39b, ex40a, ex42a, ex43, ex45, ex46, ex57, ex60, ex61a, ex64, ex68, ex69, ex71, ex72, ex73, ex77]

end HeimLasnikMay1991.Examples
