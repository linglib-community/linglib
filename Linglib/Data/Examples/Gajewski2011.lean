module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Gajewski2011` — typed example data

Auto-generated from `Linglib/Data/Examples/Gajewski2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gajewski2011.Examples`.
-/

@[expose] public section

namespace Gajewski2011.Examples

def ex14a : Datum :=
  { id := "gajewski2011_ex14a"
    source := ⟨"gajewski-2011", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No doctor has seen anyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "weak"), ("npi", "anyone")] }

def ex15a : Datum :=
  { id := "gajewski2011_ex15a"
    source := ⟨"gajewski-2011", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No doctor has seen Mary in weeks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "no"), ("strength", "strong"), ("npi", "in weeks")] }

def ex14b : Datum :=
  { id := "gajewski2011_ex14b"
    source := ⟨"gajewski-2011", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most 5 doctors have seen anyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "atMostFive"), ("strength", "weak"), ("npi", "anyone")] }

def ex15b : Datum :=
  { id := "gajewski2011_ex15b"
    source := ⟨"gajewski-2011", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most 5 doctors have seen Mary in weeks."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "atMostFive"), ("strength", "strong"), ("npi", "in weeks")] }

def ex1f : Datum :=
  { id := "gajewski2011_ex1f"
    source := ⟨"gajewski-2011", "(1f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students ever said anything."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "some"), ("strength", "weak"), ("npi", "ever")] }

def ex7f : Datum :=
  { id := "gajewski2011_ex7f"
    source := ⟨"gajewski-2011", "(7f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students left until their birthdays."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "some"), ("strength", "strong"), ("npi", "until")] }

def ex39a : Datum :=
  { id := "gajewski2011_ex39a"
    source := ⟨"gajewski-2011", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John has ever seen anyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "weak"), ("npi", "ever, anyone")] }

def ex39b : Datum :=
  { id := "gajewski2011_ex39b"
    source := ⟨"gajewski-2011", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John has seen Mary in weeks."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "in weeks")] }

def ex39c : Datum :=
  { id := "gajewski2011_ex39c"
    source := ⟨"gajewski-2011", "(39c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John likes pancakes, either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "either")] }

def ex39d : Datum :=
  { id := "gajewski2011_ex39d"
    source := ⟨"gajewski-2011", "(39d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John arrived until his birthday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "only"), ("strength", "strong"), ("npi", "until")] }

def ex40a : Datum :=
  { id := "gajewski2011_ex40a"
    source := ⟨"gajewski-2011", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill has ever seen anyone, he is keeping it a secret."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "weak"), ("npi", "ever, anyone")] }

def ex40b : Datum :=
  { id := "gajewski2011_ex40b"
    source := ⟨"gajewski-2011", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill has seen Mary in weeks, he is keeping it a secret."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "in weeks")] }

def ex40c : Datum :=
  { id := "gajewski2011_ex40c"
    source := ⟨"gajewski-2011", "(40c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill likes pancakes, either, he is keeping it a secret."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "either")] }

def ex40d : Datum :=
  { id := "gajewski2011_ex40d"
    source := ⟨"gajewski-2011", "(40d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill arrived until Friday, he is keeping it a secret."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "conditional"), ("strength", "strong"), ("npi", "until")] }

def ex41a : Datum :=
  { id := "gajewski2011_ex41a"
    source := ⟨"gajewski-2011", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she ever talked to anyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "weak"), ("npi", "ever, anyone")] }

def ex41b : Datum :=
  { id := "gajewski2011_ex41b"
    source := ⟨"gajewski-2011", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she has talked to Bill in weeks."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "in weeks")] }

def ex41c : Datum :=
  { id := "gajewski2011_ex41c"
    source := ⟨"gajewski-2011", "(41c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she likes pancakes, either."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "either")] }

def ex41d : Datum :=
  { id := "gajewski2011_ex41d"
    source := ⟨"gajewski-2011", "(41d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is sorry that she arrived until Friday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("licenser", "sorry"), ("strength", "strong"), ("npi", "until")] }

def all : List Datum := [ex14a, ex15a, ex14b, ex15b, ex1f, ex7f, ex39a, ex39b, ex39c, ex39d, ex40a, ex40b, ex40c, ex40d, ex41a, ex41b, ex41c, ex41d]

/-- Weak items are *any* and *ever*, strong ones *in weeks*, *either* and *until*. -/
inductive Strength where
  /-- weak: weak -/
  | weak
  /-- strong: strong -/
  | strong
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `strength`. -/
def strength (e : Datum) : Option Strength :=
  e.parse? "strength" [("weak", .weak), ("strong", .strong)]

end Gajewski2011.Examples
