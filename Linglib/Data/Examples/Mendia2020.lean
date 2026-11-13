module

public import Linglib.Data.Examples.Schema

/-!
# `Mendia2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Mendia2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Mendia2020.Examples`.
-/

@[expose] public section

namespace Mendia2020.Examples

def ex_14a : Datum :=
  { id := "mendia2020_14a"
    source := ⟨"mendia-2020", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two kinds of dog are sitting in the next room."
    glossedTokens := []
    context := "There are three bull-dogs and two beagles in the next room."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "mendia2020_14b"
    source := ⟨"mendia-2020", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two kinds of dog are sitting in the next room."
    glossedTokens := []
    context := "There is only Fido, who is a border collie and a watch-dog, in the next room."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_32a : Datum :=
  { id := "mendia2020_32a"
    source := ⟨"mendia-2020", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of dog is dangerous."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_32b : Datum :=
  { id := "mendia2020_32b"
    source := ⟨"mendia-2020", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kind of dog is dangerous."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn9_ia : Datum :=
  { id := "mendia2020_fn9_ia"
    source := ⟨"mendia-2020", "fn. 9 (i-a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These days, the dogs that bite humans are especially dangerous."
    glossedTokens := []
    context := "The rabies vaccine is now ineffective because of a mutation that the virus has undergone. So one must be very careful not to get bit by potentially rabies-carrying animals."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn9_ib : Datum :=
  { id := "mendia2020_fn9_ib"
    source := ⟨"mendia-2020", "fn. 9 (i-b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These days, the dogs are especially dangerous."
    glossedTokens := []
    context := "The rabies vaccine is now ineffective because of a mutation that the virus has undergone. So one must be very careful not to get bit by potentially rabies-carrying animals."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_14a, ex_14b, ex_32a, ex_32b, fn9_ia, fn9_ib]

end Mendia2020.Examples
