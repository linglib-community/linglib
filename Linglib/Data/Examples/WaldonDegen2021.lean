module

public import Linglib.Data.Examples.Schema

/-!
# `WaldonDegen2021` — typed example data

Auto-generated from `Linglib/Data/Examples/WaldonDegen2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WaldonDegen2021.Examples`.
-/

@[expose] public section

namespace WaldonDegen2021.Examples

def ex_1 : Datum :=
  { id := "waldondegen2021_1"
    source := ⟨"waldon-degen-2021", "(1)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "La tachuela azul pequeña"
    glossedTokens := [("La", "det.def.f.sg"), ("tachuela", "pin"), ("azul", "blue"), ("pequeña", "small.f.sg")]
    context := ""
    judgment := .acceptable
    alternatives := [("La tachuela pequeña azul", .ungrammatical)]
    readings := []
    paperFeatures := [("idiolect", "Spanish-postnominal"), ("order", "noun color size")] }

def ex_2a : Datum :=
  { id := "waldondegen2021_2a"
    source := ⟨"waldon-degen-2021", "(2a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "La tachuela azul y pequeña"
    glossedTokens := [("La", "det.f.sg"), ("tachuela", "pin"), ("azul", "blue"), ("y", "and"), ("pequeña", "small.f.sg")]
    context := ""
    judgment := .acceptable
    alternatives := [("La tachuela pequeña y azul", .acceptable)]
    readings := []
    paperFeatures := [("idiolect", "Spanish-postnominal-conjunctive"), ("order", "suspended under conjunction")] }

def ex_3a : Datum :=
  { id := "waldondegen2021_3a"
    source := ⟨"waldon-degen-2021", "(3a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "La pequeña tachuela azul"
    glossedTokens := [("La", "det.f.sg"), ("pequeña", "small.f.sg"), ("tachuela", "pin"), ("azul", "blue")]
    context := ""
    judgment := .acceptable
    alternatives := [("La azul tachuela pequeña", .ungrammatical)]
    readings := []
    paperFeatures := [("idiolect", "Spanish-split"), ("order", "size noun color")] }

def all : List Datum := [ex_1, ex_2a, ex_3a]

end WaldonDegen2021.Examples
