module

public import Linglib.Data.Examples.Schema

/-!
# `Yalcin2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Yalcin2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yalcin2007.Examples`.
-/

@[expose] public section

namespace Yalcin2007.Examples

def ex_1 : Datum :=
  { id := "yalcin2007_1"
    source := ⟨"yalcin-2007", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is raining and I do not know that it is raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "Moore-paradoxical"), ("embedding", "none")] }

def ex_2 : Datum :=
  { id := "yalcin2007_2"
    source := ⟨"yalcin-2007", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not raining and for all I know, it is raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "Moore-paradoxical"), ("embedding", "none")] }

def ex_3 : Datum :=
  { id := "yalcin2007_3"
    source := ⟨"yalcin-2007", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is raining and it might not be raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("embedding", "suppose")] }

def ex_4 : Datum :=
  { id := "yalcin2007_4"
    source := ⟨"yalcin-2007", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is not raining and it might be raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("embedding", "suppose")] }

def ex_5 : Datum :=
  { id := "yalcin2007_5"
    source := ⟨"yalcin-2007", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is raining and possibly it is not raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("embedding", "suppose")] }

def ex_6 : Datum :=
  { id := "yalcin2007_6"
    source := ⟨"yalcin-2007", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is raining and it might not be raining, then …"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("embedding", "conditional antecedent")] }

def ex_7 : Datum :=
  { id := "yalcin2007_7"
    source := ⟨"yalcin-2007", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is raining and it might not be raining, then (still) it is raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("embedding", "conditional antecedent")] }

def ex_8 : Datum :=
  { id := "yalcin2007_8"
    source := ⟨"yalcin-2007", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is raining and I do not know that it is raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "Moore-paradoxical"), ("embedding", "suppose")] }

def ex_9 : Datum :=
  { id := "yalcin2007_9"
    source := ⟨"yalcin-2007", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is not raining and for all I know, it is raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "Moore-paradoxical"), ("embedding", "suppose")] }

def ex_10 : Datum :=
  { id := "yalcin2007_10"
    source := ⟨"yalcin-2007", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is raining and I do not know it, then there is something I do not know."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "Moore-paradoxical"), ("embedding", "conditional antecedent")] }

def ex_11 : Datum :=
  { id := "yalcin2007_11"
    source := ⟨"yalcin-2007", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is not raining but for all I know, it is, then there is something I do not know."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "Moore-paradoxical"), ("embedding", "conditional antecedent")] }

def ex_12 : Datum :=
  { id := "yalcin2007_12"
    source := ⟨"yalcin-2007", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is not raining and it might be raining, then for all I know, it is raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("embedding", "conditional antecedent")] }

def ex_13 : Datum :=
  { id := "yalcin2007_13"
    source := ⟨"yalcin-2007", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Vann believes that Bob might be in his office."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the modal quantifies over Vann's belief worlds", .acceptable)]
    paperFeatures := [("embedding", "believe")] }

def ex_14 : Datum :=
  { id := "yalcin2007_14"
    source := ⟨"yalcin-2007", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fido thinks there might be an intruder downstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "think")] }

def ex_15 : Datum :=
  { id := "yalcin2007_15"
    source := ⟨"yalcin-2007", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cheerios may reduce the risk of heart disease."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "expert information")] }

def ex_16 : Datum :=
  { id := "yalcin2007_16"
    source := ⟨"yalcin-2007", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I do not know whether the late Antarctic spring might be caused by ozone depletion."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "target information state")] }

def ex_17 : Datum :=
  { id := "yalcin2007_17"
    source := ⟨"yalcin-2007", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is not raining and it must be raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("modal", "must"), ("embedding", "suppose")] }

def ex_18 : Datum :=
  { id := "yalcin2007_18"
    source := ⟨"yalcin-2007", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is not raining and it is likely that it is raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("modal", "probability"), ("embedding", "suppose")] }

def ex_19 : Datum :=
  { id := "yalcin2007_19"
    source := ⟨"yalcin-2007", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it is raining and it probably is not raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("modal", "probability"), ("embedding", "suppose")] }

def ex_20 : Datum :=
  { id := "yalcin2007_20"
    source := ⟨"yalcin-2007", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is not raining and it is probably raining, then …"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "epistemic contradiction"), ("modal", "probability"), ("embedding", "conditional antecedent")] }

def ex_21 : Datum :=
  { id := "yalcin2007_21"
    source := ⟨"yalcin-2007", "(C1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the butler did not do it, the gardener did."
    glossedTokens := []
    context := "Either the butler or the gardener did it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("consequent", "plain")] }

def ex_22 : Datum :=
  { id := "yalcin2007_22"
    source := ⟨"yalcin-2007", "(C2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the butler did not do it, the gardener must have."
    glossedTokens := []
    context := "Either the butler or the gardener did it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("consequent", "must")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22]

end Yalcin2007.Examples
