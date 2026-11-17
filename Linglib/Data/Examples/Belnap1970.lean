module

public import Linglib.Data.Examples.Schema

/-!
# `Belnap1970` — typed example data

Auto-generated from `Linglib/Data/Examples/Belnap1970.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belnap1970.Examples`.
-/

@[expose] public section

namespace Belnap1970.Examples

def ex_11 : Datum :=
  { id := "belnap1970_11"
    source := ⟨"belnap-1970", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All crows are black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("quantified conditional assertion: consider the crows — each one is black", .acceptable)]
    paperFeatures := [("form", "A"), ("assertive iff", "there are crows")] }

def ex_12 : Datum :=
  { id := "belnap1970_12"
    source := ⟨"belnap-1970", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some crows are black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("consider the crows: some of them are black", .acceptable)]
    paperFeatures := [("form", "I"), ("assertive iff", "there are crows")] }

def unicorns_a : Datum :=
  { id := "belnap1970_unicorns_a"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some unicorns are animals."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("status", "nonassertive"), ("diagnostic", "I-conversion")] }

def unicorns_b : Datum :=
  { id := "belnap1970_unicorns_b"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some animals are unicorns."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("status", "false"), ("diagnostic", "I-conversion")] }

def johns_children : Datum :=
  { id := "belnap1970_johns_children"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of John's children are asleep."
    glossedTokens := []
    context := "John has no children."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("status", "nonassertive"), ("diagnostic", "I-conversion")] }

def barbara : Datum :=
  { id := "belnap1970_barbara"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of Alan's birds are black."
    glossedTokens := []
    context := "Major: all crows are black. Minor: all of Alan's birds are crows."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "Barbara conclusion"), ("asymmetry", "the major alone implies the conclusion")] }

def biscuits : Datum :=
  { id := "belnap1970_biscuits"
    source := ⟨"belnap-1970", "p. 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are biscuits on the sideboard if you want some."
    glossedTokens := []
    context := "There are no biscuits, and you don't want any."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("status", "plain false, not nonassertive")] }

def frank_james : Datum :=
  { id := "belnap1970_frank_james"
    source := ⟨"belnap-1970", "p. 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If my name is Frank James, I have never beaten my wife."
    glossedTokens := []
    context := "A reply to: If your name is Frank James, have you stopped beating your wife?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "conditional denial of a conditional question's presupposition")] }

def wages : Datum :=
  { id := "belnap1970_wages"
    source := ⟨"belnap-1970", "p. 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wages were high throughout the 1960's."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("use", "summarizing an empirical regularity without explanatory force")] }

def all : List Datum := [ex_11, ex_12, unicorns_a, unicorns_b, johns_children, barbara, biscuits, frank_james, wages]

end Belnap1970.Examples
