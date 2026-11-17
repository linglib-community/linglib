module

public import Linglib.Data.Examples.Schema

/-!
# `CiardelliGuerrini2026` — typed example data

Auto-generated from `Linglib/Data/Examples/CiardelliGuerrini2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CiardelliGuerrini2026.Examples`.
-/

@[expose] public section

namespace CiardelliGuerrini2026.Examples

def ex2 : Datum :=
  { id := "ciardelliguerrini2026_ex2"
    source := ⟨"ciardelli-guerrini-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may do A or you may do B."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .acceptable), ("ignorance", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "or"), ("narrowReading", "free choice")] }

def ex5 : Datum :=
  { id := "ciardelliguerrini2026_ex5"
    source := ⟨"ciardelli-guerrini-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Either) you must write an essay or you must give a presentation."
    glossedTokens := []
    context := "Alice asks Bob how one can get credit for a certain course."
    judgment := .acceptable
    contrasts := []
    readings := [("disjunctive obligation", .acceptable), ("ignorance", .acceptable)]
    paperFeatures := [("modal1", "must"), ("modal2", "must"), ("coordinator", "or"), ("narrowReading", "disjunctive obligation")] }

def ex7 : Datum :=
  { id := "ciardelliguerrini2026_ex7"
    source := ⟨"ciardelli-guerrini-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may go to Bob's party and you may go to Charlie's party."
    glossedTokens := []
    context := "Alice's friends Bob, Charlie and Diana each invited her to their birthday party this week. Mom says she cannot go to Diana's party, then:"
    judgment := .acceptable
    contrasts := []
    readings := [("conjunctive permission", .acceptable), ("conjunction of permissions", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "and"), ("narrowReading", "conjunctive permission")] }

def ex9b : Datum :=
  { id := "ciardelliguerrini2026_ex9b"
    source := ⟨"ciardelli-guerrini-2026", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may come with me and you may stay here."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := [("conjunctive permission", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "and"), ("narrowReading", "conjunctive permission")] }

def ex19a : Datum :=
  { id := "ciardelliguerrini2026_ex19a"
    source := ⟨"ciardelli-guerrini-2026", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's ok for John to sing or it's ok for John to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("modal1", "it's ok"), ("modal2", "it's ok"), ("coordinator", "or")] }

def ex19b_allowed : Datum :=
  { id := "ciardelliguerrini2026_ex19b_allowed"
    source := ⟨"ciardelli-guerrini-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is allowed to sing or he is allowed to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("modal1", "be allowed"), ("modal2", "be allowed"), ("coordinator", "or")] }

def ex19b_required : Datum :=
  { id := "ciardelliguerrini2026_ex19b_required"
    source := ⟨"ciardelli-guerrini-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required to sing or he is required to dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .unacceptable)]
    paperFeatures := [("modal1", "be required"), ("modal2", "be required"), ("coordinator", "or")] }

def ex22a : Datum :=
  { id := "ciardelliguerrini2026_ex22a"
    source := ⟨"ciardelli-guerrini-2026", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John may either sing or he may dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "or"), ("narrowReading", "free choice")] }

def ex22b : Datum :=
  { id := "ciardelliguerrini2026_ex22b"
    source := ⟨"ciardelli-guerrini-2026", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either John may sing or he may dance."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "may"), ("coordinator", "or"), ("narrowReading", "free choice")] }

def exfn4i : Datum :=
  { id := "ciardelliguerrini2026_exfn4i"
    source := ⟨"ciardelli-guerrini-2026", "fn. 4 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may email us or you can reach the Business License office at 949 644-3141."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("free choice", .acceptable)]
    paperFeatures := [("modal1", "may"), ("modal2", "can"), ("coordinator", "or"), ("narrowReading", "free choice")] }

def ex28 : Datum :=
  { id := "ciardelliguerrini2026_ex28"
    source := ⟨"ciardelli-guerrini-2026", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I need not cook and I need not clean."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("permission to do neither", .acceptable), ("obligation to do neither", .unacceptable)]
    paperFeatures := [("modal1", "need"), ("modal2", "need"), ("coordinator", "and"), ("narrowReading", "permission to do neither"), ("negated", "true")] }

def ex11a : Datum :=
  { id := "ciardelliguerrini2026_ex11a"
    source := ⟨"ciardelli-guerrini-2026", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss allows that Alice may leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "may")] }

def ex11b : Datum :=
  { id := "ciardelliguerrini2026_ex11b"
    source := ⟨"ciardelli-guerrini-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss demands that Bob must stay."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "must")] }

def ex20a : Datum :=
  { id := "ciardelliguerrini2026_ex20a"
    source := ⟨"ciardelli-guerrini-2026", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss allows that Alice be permitted to leave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "be permitted")] }

def ex20b : Datum :=
  { id := "ciardelliguerrini2026_ex20b"
    source := ⟨"ciardelli-guerrini-2026", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boss demands that Bob be required to stay."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "be required")] }

def ex24 : Datum :=
  { id := "ciardelliguerrini2026_ex24"
    source := ⟨"ciardelli-guerrini-2026", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The countess graciously allowed that I needn't do it for her again."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "need"), ("negated", "true")] }

def ex25 : Datum :=
  { id := "ciardelliguerrini2026_ex25"
    source := ⟨"ciardelli-guerrini-2026", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A restraining order demands that Roiland may not harass or surveil the plaintiff."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("modal concord", .acceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "may"), ("negated", "true")] }

def ex26 : Datum :=
  { id := "ciardelliguerrini2026_ex26"
    source := ⟨"ciardelli-guerrini-2026", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The countess firmly demanded that I needn't do it for her again."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "demand"), ("checked", "need"), ("negated", "true")] }

def ex27 : Datum :=
  { id := "ciardelliguerrini2026_ex27"
    source := ⟨"ciardelli-guerrini-2026", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A special permit allows that Roiland may not recycle."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := [("modal concord", .unacceptable)]
    paperFeatures := [("checker", "allow"), ("checked", "may"), ("negated", "true")] }

def all : List Datum := [ex2, ex5, ex7, ex9b, ex19a, ex19b_allowed, ex19b_required, ex22a, ex22b, exfn4i, ex28, ex11a, ex11b, ex20a, ex20b, ex24, ex25, ex26, ex27]

end CiardelliGuerrini2026.Examples
