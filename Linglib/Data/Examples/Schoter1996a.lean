module

public import Linglib.Data.Examples.Schema

/-!
# `Schoter1996a` — typed example data

Auto-generated from `Linglib/Data/Examples/Schoter1996a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schoter1996a.Examples`.
-/

@[expose] public section

namespace Schoter1996a.Examples

def ex6_10a : Datum :=
  { id := "schoter1996a_ex6_10a"
    source := ⟨"schoter-1996a", "(6.10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't regret failing the exam because, in fact, he passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex6_10b : Datum :=
  { id := "schoter1996a_ex6_10b"
    source := ⟨"schoter-1996a", "(6.10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John regrets failing the exam but, in fact, he passed."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex6_11a : Datum :=
  { id := "schoter1996a_ex6_11a"
    source := ⟨"schoter-1996a", "(6.11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John regrets failing the exam. Therefore, John failed the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex6_11b : Datum :=
  { id := "schoter1996a_ex6_11b"
    source := ⟨"schoter-1996a", "(6.11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't regret failing the exam. So, John failed the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex6_11c : Datum :=
  { id := "schoter1996a_ex6_11c"
    source := ⟨"schoter-1996a", "(6.11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John regrets failing the exam because, in fact, he didn't fail."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex6_11d : Datum :=
  { id := "schoter1996a_ex6_11d"
    source := ⟨"schoter-1996a", "(6.11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't regret failing the exam because, in fact, he didn't fail."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex6_11e : Datum :=
  { id := "schoter1996a_ex6_11e"
    source := ⟨"schoter-1996a", "(6.11e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't fail the exam — so he doesn't regret failing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex6_10a, ex6_10b, ex6_11a, ex6_11b, ex6_11c, ex6_11d, ex6_11e]

end Schoter1996a.Examples
