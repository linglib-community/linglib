module

public import Linglib.Data.Examples.Schema

/-!
# `Ahn2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Ahn2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ahn2015.Examples`.
-/

@[expose] public section

namespace Ahn2015.Examples

def ex_1 : Datum :=
  { id := "ahn2015_1"
    source := ⟨"ahn-2015", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John came to the party too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("focus", "John")] }

def ex_2 : Datum :=
  { id := "ahn2015_2"
    source := ⟨"ahn-2015", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't come to the party either."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative"), ("focus", "John")] }

def ex_3 : Datum :=
  { id := "ahn2015_3"
    source := ⟨"ahn-2015", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We're going to Philly either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive")] }

def ex_5_too : Datum :=
  { id := "ahn2015_5_too"
    source := ⟨"rullmann-2003", ""⟩
    reportedIn := some ⟨"ahn-2015", "(5)"⟩
    language := "stan1293"
    primaryText := "John washed the dishes. He shouldn't do the laundry too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("antecedent", "positive")] }

def ex_5_either : Datum :=
  { id := "ahn2015_5_either"
    source := ⟨"rullmann-2003", ""⟩
    reportedIn := some ⟨"ahn-2015", "(5)"⟩
    language := "stan1293"
    primaryText := "John washed the dishes. He shouldn't do the laundry either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative"), ("antecedent", "positive")] }

def ex_9 : Datum :=
  { id := "ahn2015_9"
    source := ⟨"ahn-2015", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't leave either."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative")] }

def ex_10 : Datum :=
  { id := "ahn2015_10"
    source := ⟨"ahn-2015", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive")] }

def ex_11 : Datum :=
  { id := "ahn2015_11"
    source := ⟨"ahn-2015", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is almost finished either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive"), ("operator", "almost")] }

def ex_12 : Datum :=
  { id := "ahn2015_12"
    source := ⟨"ahn-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is having dinner in New York tonight too."
    glossedTokens := []
    context := "Uttered out of the blue; it is common knowledge that many people dine in New York every night."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("focus", "John"), ("felicity", "infelicitous")] }

def ex_15 : Datum :=
  { id := "ahn2015_15"
    source := ⟨"ahn-2015", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John is coming to the party, the boss will come too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("distinctness", "John and the boss must be distinct")] }

def ex_23 : Datum :=
  { id := "ahn2015_23"
    source := ⟨"ahn-2015", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't visit Boston. Bill didn't visit Boston too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "negative"), ("scope", "negation below too")] }

def ex_24 : Datum :=
  { id := "ahn2015_24"
    source := ⟨"ahn-2015", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue bought some books. (But) Mary didn't buy them too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "negative"), ("scope", "negation above too")] }

def ex_26a : Datum :=
  { id := "ahn2015_26a"
    source := ⟨"ahn-2015", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary went to the shop, but it is not the case that somebody went there."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "none"), ("test", "Abrusán entailment")] }

def ex_26b : Datum :=
  { id := "ahn2015_26b"
    source := ⟨"ahn-2015", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary went to the shop, but it is not the case that somebody went there as well."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "as well"), ("test", "Abrusán entailment")] }

def ex_29 : Datum :=
  { id := "ahn2015_29"
    source := ⟨"ahn-2015", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't know if Mary is in the elevator. But if John is in the elevator too, we will go over the weight limit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("antecedent", "not presupposed")] }

def ex_32 : Datum :=
  { id := "ahn2015_32"
    source := ⟨"ahn-2015", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't leave either."
    glossedTokens := []
    context := "Discourse antecedent or context entailing that Bill didn't leave."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative"), ("focus", "John")] }

def ex_41 : Datum :=
  { id := "ahn2015_41"
    source := ⟨"ahn-2015", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive")] }

def ex_43 : Datum :=
  { id := "ahn2015_43"
    source := ⟨"ahn-2015", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't leave either."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative")] }

def ex_45 : Datum :=
  { id := "ahn2015_45"
    source := ⟨"ahn-2015", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is almost finished either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive"), ("operator", "almost")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_5_too, ex_5_either, ex_9, ex_10, ex_11, ex_12, ex_15, ex_23, ex_24, ex_26a, ex_26b, ex_29, ex_32, ex_41, ex_43, ex_45]

end Ahn2015.Examples
