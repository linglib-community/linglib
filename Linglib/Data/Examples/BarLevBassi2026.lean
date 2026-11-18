module

public import Linglib.Data.Examples.Schema

/-!
# `BarLevBassi2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BarLevBassi2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarLevBassi2026.Examples`.
-/

@[expose] public section

namespace BarLevBassi2026.Examples

def ex_3 : Datum :=
  { id := "barlevbassi2026_3"
    source := ⟨"bar-lev-bassi-2026", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she read the books."
    glossedTokens := []
    context := "I knew that Ann read at least some of the books. But today I learned that..."
    judgment := .unacceptable
    contrasts := [("she read ALL the books.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_9 : Datum :=
  { id := "barlevbassi2026_9"
    source := ⟨"bar-lev-bassi-2026", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she didn't read the books."
    glossedTokens := []
    context := "I knew that Ann didn't read all of the books. But today I learned that..."
    judgment := .unacceptable
    contrasts := [("she didn't read ANY of the books.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_11 : Datum :=
  { id := "barlevbassi2026_11"
    source := ⟨"bar-lev-bassi-2026", "(11), (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann read the books."
    glossedTokens := []
    context := "Did Ann read some of the books, or all of them?"
    judgment := .unacceptable
    contrasts := [("Ann read ALL the books.", .acceptable), ("Ann read all the books.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_13_i : Datum :=
  { id := "barlevbassi2026_13_i"
    source := ⟨"bar-lev-bassi-2026", "(13a-i), (13b), (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann read the books."
    glossedTokens := []
    context := "Did Ann read none of the books, some of the books, or all of the books?"
    judgment := .unacceptable
    contrasts := [("Ann read ALL the books.", .acceptable), ("Ann read all the books.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_13_ii : Datum :=
  { id := "barlevbassi2026_13_ii"
    source := ⟨"bar-lev-bassi-2026", "(13a-ii), (13b), (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann read the books."
    glossedTokens := []
    context := "Did Ann read none of the books, or all of them?"
    judgment := .unacceptable
    contrasts := [("Ann read ALL the books.", .acceptable), ("Ann read all the books.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_15 : Datum :=
  { id := "barlevbassi2026_15"
    source := ⟨"bar-lev-bassi-2026", "(15), (22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Today she read the newspapers."
    glossedTokens := []
    context := "Yesterday she read some of the newspapers."
    judgment := .unacceptable
    contrasts := [("Today she read ALL the newspapers.", .acceptable), ("Today she read all the newspapers.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_16 : Datum :=
  { id := "barlevbassi2026_16"
    source := ⟨"bar-lev-bassi-2026", "(16), (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "B: No, don't worry, she DID read the books."
    glossedTokens := []
    context := "A: I know that Mary read some of the books, but I suspect that she didn't read all of them."
    judgment := .acceptable
    contrasts := [("B': No, don't worry, she DID read all the books.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_17 : Datum :=
  { id := "barlevbassi2026_17"
    source := ⟨"bar-lev-bassi-2026", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "B: No, don't worry, she DID stop smoking."
    glossedTokens := []
    context := "A: I know that Mary doesn't smoke now, but I'm worried that she also didn't smoke in the past (in which case she is not a good fit for our experiment)."
    judgment := .unacceptable
    contrasts := [("B': No, don't worry, she DID smoke in the past.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_19 : Datum :=
  { id := "barlevbassi2026_19"
    source := ⟨"bar-lev-bassi-2026", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she read the books."
    glossedTokens := []
    context := "I knew that Ann read at least one of the books. But today I learned that..."
    judgment := .unacceptable
    contrasts := [("she read ALL the books.", .acceptable), ("she read all the books.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_20 : Datum :=
  { id := "barlevbassi2026_20"
    source := ⟨"bar-lev-bassi-2026", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she didn't read the books."
    glossedTokens := []
    context := "I knew that Ann didn't read at least one of the books. But today I learned that..."
    judgment := .unacceptable
    contrasts := [("she didn't read ANY of the books.", .acceptable), ("she didn't read any of the books.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_37 : Datum :=
  { id := "barlevbassi2026_37"
    source := ⟨"bar-lev-bassi-2026", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: No, she DID read the books."
    glossedTokens := []
    context := "Q: Did she not read all the books?"
    judgment := .acceptable
    contrasts := [("A: No, she DID read all the books.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_38 : Datum :=
  { id := "barlevbassi2026_38"
    source := ⟨"bar-lev-bassi-2026", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he worked on his phonology papers today."
    glossedTokens := []
    context := "John really likes to write phonology papers. Every day, he either works on some of them or all of them. He is in a cheerful mood now, so apparently..."
    judgment := .unacceptable
    contrasts := [("he worked on ALL of his phonology papers today.", .acceptable), ("he worked on all of his phonology papers today.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_39 : Datum :=
  { id := "barlevbassi2026_39"
    source := ⟨"bar-lev-bassi-2026", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he worked on his PHONOLOGY papers today."
    glossedTokens := []
    context := "John really likes to write phonology papers. He also writes semantics papers, but he hates that. Every day, he either works on all of his phonology papers and none of his semantics papers, or all of his semantics papers and some of his phonology papers. He is in a cheerful mood, so apparently..."
    judgment := .acceptable
    contrasts := [("he worked on all of his PHONOLOGY papers today.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_41 : Datum :=
  { id := "barlevbassi2026_41"
    source := ⟨"bar-lev-bassi-2026", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not married to his teammates."
    glossedTokens := []
    context := "A monogamous society."
    judgment := .unacceptable
    contrasts := [("John is not married to any of his teammates.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_42 : Datum :=
  { id := "barlevbassi2026_42"
    source := ⟨"bar-lev-bassi-2026", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I checked in during round three and my uncles were still in the game."
    glossedTokens := []
    context := "In a game of Knuckle, at the end of each round, the person who has more cards than anybody else cashes in and leaves the game. If at the end of a round no player has more cards than anybody else, then all the players stay in the game. Last Saturday night, 5 of my uncles sat down for a long game of Knuckle."
    judgment := .unacceptable
    contrasts := [("I checked in during round three and all my uncles were still in the game.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_44 : Datum :=
  { id := "barlevbassi2026_44"
    source := ⟨"bar-lev-bassi-2026", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She read the books."
    glossedTokens := []
    context := "Did she read any of the books?"
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_45 : Datum :=
  { id := "barlevbassi2026_45"
    source := ⟨"bar-lev-bassi-2026", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "she's not MARRIED to those people (so it may not look good but it's not illegal)."
    glossedTokens := []
    context := "The mayor is friends with some of the people building the highway, but..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def fn18_i : Datum :=
  { id := "barlevbassi2026_fn18_i"
    source := ⟨"bar-lev-bassi-2026", "fn. 18 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: No, she is NOT married to her teammates."
    glossedTokens := []
    context := "Q: Is she married to any of her teammates?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_3, ex_9, ex_11, ex_13_i, ex_13_ii, ex_15, ex_16, ex_17, ex_19, ex_20, ex_37, ex_38, ex_39, ex_41, ex_42, ex_44, ex_45, fn18_i]

end BarLevBassi2026.Examples
