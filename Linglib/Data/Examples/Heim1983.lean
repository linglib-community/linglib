module

public import Linglib.Data.Examples.Schema

/-!
# `Heim1983` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1983.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1983.Examples`.
-/

@[expose] public section

namespace Heim1983.Examples

def ex1 : Datum :=
  { id := "heim1983_ex1"
    source := ⟨"heim-1983", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king has a son."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "0"), ("presupposes", "there is a king")] }

def ex2 : Datum :=
  { id := "heim1983_ex2"
    source := ⟨"heim-1983", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king's son is bald."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "0"), ("presupposes", "the king has a son")] }

def ex3 : Datum :=
  { id := "heim1983_ex3"
    source := ⟨"heim-1983", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the king has a son, the king's son is bald."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "0"), ("presupposes", "there is a king"), ("filtered", "the king has a son")] }

def ex5 : Datum :=
  { id := "heim1983_ex5"
    source := ⟨"heim-1983", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John has children, then Mary will not like his twins."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2"), ("presupposes", "someone with children has twins"), ("gazdar", "nothing"), ("kp", "as reported")] }

def ex6 : Datum :=
  { id := "heim1983_ex6"
    source := ⟨"heim-1983", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John has twins, then Mary will not like his children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2"), ("presupposes", "nothing"), ("gazdar", "John has children"), ("kp", "nothing")] }

def ex7 : Datum :=
  { id := "heim1983_ex7"
    source := ⟨"heim-1983", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every nation cherishes its king."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.3"), ("presupposes", "every nation has a king"), ("kp", "every nation has a king")] }

def ex16 : Datum :=
  { id := "heim1983_ex16"
    source := ⟨"heim-1983", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king of France didn't come."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.3"), ("global", "France has a king"), ("local", "either France has no king or he didn't come")] }

def ex23 : Datum :=
  { id := "heim1983_ex23"
    source := ⟨"heim-1983", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who serves his king will be rewarded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("presupposes", "everyone has a king"), ("kp", "nothing")] }

def ex24 : Datum :=
  { id := "heim1983_ex24"
    source := ⟨"heim-1983", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No nation cherishes its king."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("cooper", "every nation has a king"), ("lernerZimmermann", "some nation has a king")] }

def ex25 : Datum :=
  { id := "heim1983_ex25"
    source := ⟨"heim-1983", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A fat man was pushing his bicycle."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("kp", "some fat man had a bicycle"), ("presupposes", "every fat man had a bicycle, unless accommodated")] }

def all : List Datum := [ex1, ex2, ex3, ex5, ex6, ex7, ex16, ex23, ex24, ex25]

end Heim1983.Examples
