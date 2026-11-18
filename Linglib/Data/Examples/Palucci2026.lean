module

public import Linglib.Data.Examples.Schema

/-!
# `Palucci2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Palucci2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Palucci2026.Examples`.
-/

@[expose] public section

namespace Palucci2026.Examples

def ex_2 : Datum :=
  { id := "palucci2026_2"
    source := ⟨"palucci-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John included the supervisor that each volunteer reported to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("single supervisor", .acceptable), ("varying definite", .acceptable)]
    paperFeatures := [] }

def ex_5a : Datum :=
  { id := "palucci2026_5a"
    source := ⟨"palucci-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A student claimed each invited speaker was wrong."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > ∀", .acceptable), ("∀ > ∃", .unacceptable)]
    paperFeatures := [] }

def ex_6a : Datum :=
  { id := "palucci2026_6a"
    source := ⟨"palucci-2026", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What? I included the supervisor that you claimed each volunteer reported to."
    glossedTokens := []
    context := "At the community center, each volunteer reports to a different supervisor. John is supposed to keep track of all this in a file, but he's clueless regarding who reports to whom. However, he remembers that Mary claimed that Alice reports to Bill, Chris reports to Diane, and Eric reports to Francine. After writing these supervisor/volunteer pairs in the file, Mary looks it over. She looks puzzled, so John replies:"
    judgment := .acceptable
    contrasts := []
    readings := [("varying definite", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex_2, ex_5a, ex_6a]

end Palucci2026.Examples
