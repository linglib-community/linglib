module

public import Linglib.Data.Examples.Schema

/-!
# `Musan1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Musan1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Musan1995.Examples`.
-/

@[expose] public section

namespace Musan1995.Examples

def ex2a : Datum :=
  { id := "musan1995_ex2a"
    source := ⟨"musan-1995", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gregory was silent."
    glossedTokens := []
    context := "Past tense with a stage-level predicate (`silent`). Does NOT implicate that Gregory is dead — silence is a temporary state; the sentence is felicitous regardless of Gregory's current existence."
    judgment := .acceptable
    contrasts := []
    readings := [("no-lifetime-implicature (stage-level)", .acceptable)]
    paperFeatures := [] }

def ex2b : Datum :=
  { id := "musan1995_ex2b"
    source := ⟨"musan-1995", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gregory was from America."
    glossedTokens := []
    context := "Past tense with an individual-level predicate (`from America` — a permanent origin/property). IMPLICATES that Gregory is dead. The lifetime effect: past tense + individual-level predicate → subject's lifetime has ended."
    judgment := .acceptable
    contrasts := []
    readings := [("lifetime-implicature (Gregory is dead)", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex2a, ex2b]

end Musan1995.Examples
