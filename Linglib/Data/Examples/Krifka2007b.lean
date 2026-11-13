module

public import Linglib.Data.Examples.Schema

/-!
# `Krifka2007b` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka2007b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka2007b.Examples`.
-/

@[expose] public section

namespace Krifka2007b.Examples

def ex3a : Datum :=
  { id := "krifka2007b_ex3a"
    source := ⟨"krifka-2007b", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was not unhappy to find that my kids were already awake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("quite happy", .acceptable), ("happy", .unacceptable)]
    paperFeatures := [] }

def ex9a : Datum :=
  { id := "krifka2007b_ex9a"
    source := ⟨"krifka-2007b", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm not happy at all, in fact I'm quite unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex9b : Datum :=
  { id := "krifka2007b_ex9b"
    source := ⟨"krifka-2007b", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm quite unhappy, in fact I'm not happy at all."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex11 : Datum :=
  { id := "krifka2007b_ex11"
    source := ⟨"krifka-2007b", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't happy. Well, he's not unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex21 : Datum :=
  { id := "krifka2007b_ex21"
    source := ⟨"krifka-2007b", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I am neither happy nor unhappy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex22 : Datum :=
  { id := "krifka2007b_ex22"
    source := ⟨"krifka-2007b", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Regardless whether you are a happy person or an unhappy person, you should read this book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex3a, ex9a, ex9b, ex11, ex21, ex22]

end Krifka2007b.Examples
