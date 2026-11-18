module

public import Linglib.Data.Examples.Schema

/-!
# `Franke2011` — typed example data

Auto-generated from `Linglib/Data/Examples/Franke2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Franke2011.Examples`.
-/

@[expose] public section

namespace Franke2011.Examples

def ex4 : Datum :=
  { id := "franke2011_ex4"
    source := ⟨"franke-2011", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of Kiki's friends are metalheads."
    glossedTokens := []
    context := "Contrasted with 'All of Kiki's friends are metalheads' (5)."
    judgment := .acceptable
    contrasts := []
    readings := [("general epistemic: speaker does not believe all (6a)", .acceptable), ("strong epistemic: speaker believes not all (6b)", .acceptable), ("weak epistemic: speaker uncertain about all (6c)", .acceptable), ("base-level: not all (6d)", .acceptable)]
    paperFeatures := [] }

def ex8 : Datum :=
  { id := "franke2011_ex8"
    source := ⟨"franke-2011", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha is in love with Alf or Bert."
    glossedTokens := []
    context := "Alternatives (9): Alf; Bert; Alf and Bert."
    judgment := .acceptable
    contrasts := []
    readings := [("ignorance: speaker uncertain about each disjunct (10)", .acceptable), ("exclusivity: not both (11)", .acceptable)]
    paperFeatures := [] }

def ex12a : Datum :=
  { id := "franke2011_ex12a"
    source := ⟨"franke-2011", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take an apple or a pear."
    glossedTokens := []
    context := "Alternatives (17): may take an apple; may take a pear; may take both."
    judgment := .acceptable
    contrasts := []
    readings := [("free choice: may take an apple and may take a pear (12b)", .acceptable), ("exclusivity: may not take both (15d)", .acceptable)]
    paperFeatures := [] }

def ex13 : Datum :=
  { id := "franke2011_ex13"
    source := ⟨"franke-2011", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take an apple or a pear, but I don't know which."
    glossedTokens := []
    context := "The speaker's authority over the permission is suspended."
    judgment := .acceptable
    contrasts := []
    readings := [("ignorance: speaker uncertain whether the hearer may take an apple (14a)", .acceptable)]
    paperFeatures := [] }

def ex18 : Datum :=
  { id := "franke2011_ex18"
    source := ⟨"franke-2011", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you eat an apple or a pear, you will feel better."
    glossedTokens := []
    context := "Alternatives (19): if you eat an apple ...; if you eat a pear ..."
    judgment := .acceptable
    contrasts := []
    readings := [("simplification of disjunctive antecedents (19a) and (19b)", .acceptable)]
    paperFeatures := [] }

def ex30 : Datum :=
  { id := "franke2011_ex30"
    source := ⟨"franke-2011", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John had taken an apple or a pear, he would have taken an apple."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("simplification to (30b): if John had taken a pear, he would have taken an apple", .unacceptable)]
    paperFeatures := [] }

def ex95a : Datum :=
  { id := "franke2011_ex95a"
    source := ⟨"franke-2011", "(95a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John or (John and Mary)."
    glossedTokens := []
    context := "Answer to 'Who (of John and Mary) came to the party?' (93)."
    judgment := .acceptable
    contrasts := []
    readings := [("speaker knows John came and considers it possible that Mary came (95b)", .acceptable)]
    paperFeatures := [] }

def ex99 : Datum :=
  { id := "franke2011_ex99"
    source := ⟨"franke-2011", "(99)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody is allowed to take an apple or a pear."
    glossedTokens := []
    context := "Alternatives (100): everybody is allowed to take an apple; ... a pear."
    judgment := .acceptable
    contrasts := []
    readings := [("universal free choice: everybody may take an apple and everybody may take a pear", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex4, ex8, ex12a, ex13, ex18, ex30, ex95a, ex99]

end Franke2011.Examples
