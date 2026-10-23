module

public import Linglib.Data.Examples.Schema

/-!
# `Rooth1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Rooth1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rooth1992.Examples`.
-/

@[expose] public section

namespace Rooth1992.Examples

def ex_3a : Datum :=
  { id := "rooth1992_3a"
    source := ⟨"rooth-1992", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only introduced [Bill]F to Sue."
    glossedTokens := []
    context := "Mary introduced Bill and Tom to Sue, and there were no other introductions."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "Bill")] }

def ex_3b : Datum :=
  { id := "rooth1992_3b"
    source := ⟨"rooth-1992", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only introduced Bill to [Sue]F."
    glossedTokens := []
    context := "Mary introduced Bill and Tom to Sue, and there were no other introductions."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "Sue")] }

def ex_7 : Datum :=
  { id := "rooth1992_7"
    source := ⟨"rooth-1992", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary only [read]F The Recognitions."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "read")] }

def ex_11 : Datum :=
  { id := "rooth1992_11"
    source := ⟨"rooth-1992", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An [American]F farmer was talking to a [Canadian]F farmer ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "contrast")] }

def ex_16 : Datum :=
  { id := "rooth1992_16"
    source := ⟨"rooth-1992", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, I [passed]F."
    glossedTokens := []
    context := "The speaker and roommates Steve and Paul took a quiz; George asks how it went."
    judgment := .acceptable
    alternatives := []
    readings := [("the speaker did not ace the quiz", .acceptable)]
    paperFeatures := [("construction", "scale"), ("focus", "passed")] }

def ex_17 : Datum :=
  { id := "rooth1992_17"
    source := ⟨"rooth-1992", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, [I]F passed."
    glossedTokens := []
    context := "The speaker and roommates Steve and Paul took a quiz; George asks how it went."
    judgment := .acceptable
    alternatives := []
    readings := [("the roommates did not pass", .acceptable)]
    paperFeatures := [("construction", "scale"), ("focus", "I")] }

def ex_23Aa_Qa : Datum :=
  { id := "rooth1992_23Aa_Qa"
    source := ⟨"rooth-1992", "(23Aa) answering (23Qa)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Mary]F cut Bill down to size."
    glossedTokens := []
    context := "Who cut Bill down to size?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoCutBill"), ("focus", "Mary")] }

def ex_23Ab_Qa : Datum :=
  { id := "rooth1992_23Ab_Qa"
    source := ⟨"rooth-1992", "(23Ab) answering (23Qa)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary cut [Bill]F down to size."
    glossedTokens := []
    context := "Who cut Bill down to size?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoCutBill"), ("focus", "Bill")] }

def ex_23Ab_Qb : Datum :=
  { id := "rooth1992_23Ab_Qb"
    source := ⟨"rooth-1992", "(23Ab) answering (23Qb)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary cut [Bill]F down to size."
    glossedTokens := []
    context := "Who did Mary cut down to size?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoDidMaryCut"), ("focus", "Bill")] }

def ex_23Aa_Qb : Datum :=
  { id := "rooth1992_23Aa_Qb"
    source := ⟨"rooth-1992", "(23Aa) answering (23Qb)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Mary]F cut Bill down to size."
    glossedTokens := []
    context := "Who did Mary cut down to size?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qa"), ("question", "whoDidMaryCut"), ("focus", "Mary")] }

def ex_59a : Datum :=
  { id := "rooth1992_59a"
    source := ⟨"rooth-1992", "(59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she beats [me]F more often than Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("than she beats Sue", .acceptable), ("than Sue beats me", .unacceptable)]
    paperFeatures := [("construction", "ellipsis"), ("focus", "me")] }

def ex_59b : Datum :=
  { id := "rooth1992_59b"
    source := ⟨"rooth-1992", "(59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[she]F beats me more often than Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("than she beats Sue", .unacceptable), ("than Sue beats me", .acceptable)]
    paperFeatures := [("construction", "ellipsis"), ("focus", "she")] }

def ex_70 : Datum :=
  { id := "rooth1992_70"
    source := ⟨"rooth-1992", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who [grow]F rice generally only [eat]F rice."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "only"), ("focus", "eat")] }

def ex_72a : Datum :=
  { id := "rooth1992_72a"
    source := ⟨"rooth-1992", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An American farmer was talking to a [Canadian]F farmer ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "contrast")] }

def all : List Datum := [ex_3a, ex_3b, ex_7, ex_11, ex_16, ex_17, ex_23Aa_Qa, ex_23Ab_Qa, ex_23Ab_Qb, ex_23Aa_Qb, ex_59a, ex_59b, ex_70, ex_72a]

end Rooth1992.Examples
