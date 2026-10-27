module

public import Linglib.Data.Examples.Schema

/-!
# `Dowty1979` — typed example data

Auto-generated from `Linglib/Data/Examples/Dowty1979.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dowty1979.Examples`.
-/

@[expose] public section

namespace Dowty1979.Examples

def coin_heads : Datum :=
  { id := "dowty1979_coin_heads"
    source := ⟨"dowty-1979", "p. 147"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The coin is coming up heads."
    glossedTokens := []
    context := "A coin is being flipped but has not yet landed, and nothing else about the situation predetermines how it will land."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def coin_tails : Datum :=
  { id := "dowty1979_coin_tails"
    source := ⟨"dowty-1979", "p. 147"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The coin is coming up tails."
    glossedTokens := []
    context := "A coin is being flipped but has not yet landed, and nothing else about the situation predetermines how it will land."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex28 : Datum :=
  { id := "dowty1979_ex28"
    source := ⟨"dowty-1979", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was watching television when he fell asleep."
    glossedTokens := []
    context := "John fell asleep while watching television, so his watching did not extend beyond the time he fell asleep."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def all : List Datum := [coin_heads, coin_tails, ex28]

end Dowty1979.Examples
