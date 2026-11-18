module

public import Linglib.Data.Examples.Schema

/-!
# `GroveWhite2025` — typed example data

Auto-generated from `Linglib/Data/Examples/GroveWhite2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GroveWhite2025.Examples`.
-/

@[expose] public section

namespace GroveWhite2025.Examples

def ex_1a : Datum :=
  { id := "grovewhite2025_1a"
    source := ⟨"grove-white-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo loves that Mo left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "love"), ("operator", "none"), ("inference", "(2) Mo left."), ("projects", "true")] }

def ex_1b : Datum :=
  { id := "grovewhite2025_1b"
    source := ⟨"grove-white-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo doesn't love that Mo left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "love"), ("operator", "negation"), ("inference", "(2) Mo left."), ("projects", "true")] }

def ex_1c : Datum :=
  { id := "grovewhite2025_1c"
    source := ⟨"grove-white-2025", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does Jo love that Mo left?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "love"), ("operator", "question"), ("inference", "(2) Mo left."), ("projects", "true")] }

def ex_1d : Datum :=
  { id := "grovewhite2025_1d"
    source := ⟨"grove-white-2025", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo might love that Mo left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "love"), ("operator", "modal"), ("inference", "(2) Mo left."), ("projects", "true")] }

def ex_1e : Datum :=
  { id := "grovewhite2025_1e"
    source := ⟨"grove-white-2025", "(1e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Jo loves that Mo left, she'll also love that Bo left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "love"), ("operator", "conditional"), ("inference", "(2) Mo left."), ("projects", "true")] }

def ex_17_belief : Datum :=
  { id := "grovewhite2025_17_belief"
    source := ⟨"grove-white-2025", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Was Jo annoyed that Mo left?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "be annoyed"), ("operator", "question"), ("inference", "(18a) Jo believed that Mo left."), ("projects", "true")] }

def ex_17_truth : Datum :=
  { id := "grovewhite2025_17_truth"
    source := ⟨"grove-white-2025", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Was Jo annoyed that Mo left?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "be annoyed"), ("operator", "question"), ("inference", "(18b) Mo left."), ("projects", "true")] }

def ex_19 : Datum :=
  { id := "grovewhite2025_19"
    source := ⟨"grove-white-2025", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: James just found out that Harry's having a graduation party, and I can't understand why he's so upset about it. B: He didn't find out that HARRY's having a graduation party... he found out that HARRIET is having a graduation party, and HARRIET is his best friend."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "find out"), ("operator", "negation"), ("inference", "Harry is having a graduation party."), ("projects", "false")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_1e, ex_17_belief, ex_17_truth, ex_19]

end GroveWhite2025.Examples
