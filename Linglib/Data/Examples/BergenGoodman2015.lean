module

public import Linglib.Data.Examples.Schema

/-!
# `BergenGoodman2015` — typed example data

Auto-generated from `Linglib/Data/Examples/BergenGoodman2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BergenGoodman2015.Examples`.
-/

@[expose] public section

namespace BergenGoodman2015.Examples

def fragment_answer : Datum :=
  { id := "bergengoodman2015_fragment_answer"
    source := ⟨"bergen-goodman-2015", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob"
    glossedTokens := []
    context := "A: Who went to the movies?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("fragment", "Bob"), ("proposition", "Bob went to the movies")] }

def stressed_subject : Datum :=
  { id := "bergengoodman2015_stressed_subject"
    source := ⟨"bergen-goodman-2015", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "BOB went to the movies."
    glossedTokens := []
    context := "Q: Who went to the movies? (CAPS = prosodic stress)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "subject"), ("reading", "exhaustive")] }

def unstressed_subject : Datum :=
  { id := "bergengoodman2015_unstressed_subject"
    source := ⟨"bergen-goodman-2015", "(2), unstressed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob went to the movies."
    glossedTokens := []
    context := "Q: Who went to the movies?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "none"), ("reading", "nonExhaustive")] }

def all : List Datum := [fragment_answer, stressed_subject, unstressed_subject]

end BergenGoodman2015.Examples
