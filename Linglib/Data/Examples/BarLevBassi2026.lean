module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `BarLevBassi2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BarLevBassi2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarLevBassi2026.Examples`.
-/

@[expose] public section

namespace BarLevBassi2026.Examples

def ex_3a : Datum :=
  { id := "barlevbassi2026_3a"
    source := ⟨"bar-lev-bassi-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Ann read at least some of the books. But today I learned that... she read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_3b")] }

def ex_3b : Datum :=
  { id := "barlevbassi2026_3b"
    source := ⟨"bar-lev-bassi-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Ann read at least some of the books. But today I learned that... she read ALL the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "quantifier")] }

def ex_9a : Datum :=
  { id := "barlevbassi2026_9a"
    source := ⟨"bar-lev-bassi-2026", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Ann didn't read all of the books. But today I learned that... she didn't read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_9b")] }

def ex_9b : Datum :=
  { id := "barlevbassi2026_9b"
    source := ⟨"bar-lev-bassi-2026", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I knew that Ann didn't read all of the books. But today I learned that... she didn't read ANY of the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "quantifier")] }

def ex_11b : Datum :=
  { id := "barlevbassi2026_11b"
    source := ⟨"bar-lev-bassi-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Ann read some of the books, or all of them? Ann read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_21b_ii")] }

def ex_13b_i : Datum :=
  { id := "barlevbassi2026_13b_i"
    source := ⟨"bar-lev-bassi-2026", "(13a-i), (13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Ann read none of the books, some of the books, or all of the books? Ann read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_21b_ii")] }

def ex_13b_ii : Datum :=
  { id := "barlevbassi2026_13b_ii"
    source := ⟨"bar-lev-bassi-2026", "(13a-ii), (13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Ann read none of the books, or all of them? Ann read the books."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_21b_ii")] }

def ex_15 : Datum :=
  { id := "barlevbassi2026_15"
    source := ⟨"bar-lev-bassi-2026", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday she read some of the newspapers. Today she read the newspapers."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_22b")] }

def ex_16 : Datum :=
  { id := "barlevbassi2026_16"
    source := ⟨"bar-lev-bassi-2026", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I know that Mary read some of the books, but I suspect that she didn't read all of them. B: No, don't worry, she DID read the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity"), ("counterpart", "barlevbassi2026_23Bprime")] }

def ex_17B : Datum :=
  { id := "barlevbassi2026_17B"
    source := ⟨"bar-lev-bassi-2026", "(17B)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I know that Mary doesn't smoke now, but I'm worried that she also didn't smoke in the past (in which case she is not a good fit for our experiment). B: No, don't worry, she DID stop smoking."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity")] }

def ex_17Bprime : Datum :=
  { id := "barlevbassi2026_17Bprime"
    source := ⟨"bar-lev-bassi-2026", "(17B')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I know that Mary doesn't smoke now, but I'm worried that she also didn't smoke in the past (in which case she is not a good fit for our experiment). B: No, don't worry, she DID smoke in the past."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity")] }

def ex_21b_ii : Datum :=
  { id := "barlevbassi2026_21b_ii"
    source := ⟨"bar-lev-bassi-2026", "(21b-ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Ann read none of the books, some of the books, or all of them? Ann read ALL the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Ann read all the books.", .unacceptable)]
    readings := []
    paperFeatures := [("stress", "quantifier")] }

def ex_22b : Datum :=
  { id := "barlevbassi2026_22b"
    source := ⟨"bar-lev-bassi-2026", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday she read some of the newspapers. Today she read ALL the newspapers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Today she read all the newspapers.", .unacceptable)]
    readings := []
    paperFeatures := [("stress", "quantifier")] }

def ex_23Bprime : Datum :=
  { id := "barlevbassi2026_23Bprime"
    source := ⟨"bar-lev-bassi-2026", "(23B')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I know that Mary read some of the books, but I suspect that she didn't read all of them. B': No, don't worry, she DID read all the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity")] }

def ex_37 : Datum :=
  { id := "barlevbassi2026_37"
    source := ⟨"bar-lev-bassi-2026", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Did she not read all the books? A: No, she DID read the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity"), ("counterpart", "barlevbassi2026_37_all")] }

def ex_37_all : Datum :=
  { id := "barlevbassi2026_37_all"
    source := ⟨"bar-lev-bassi-2026", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Did she not read all the books? A: No, she DID read all the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity")] }

def ex_38a : Datum :=
  { id := "barlevbassi2026_38a"
    source := ⟨"bar-lev-bassi-2026", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John really likes to write phonology papers. Every day, he either works on some of them or all of them. He is in a cheerful mood now, so apparently... he worked on his phonology papers today."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_38b")] }

def ex_38b : Datum :=
  { id := "barlevbassi2026_38b"
    source := ⟨"bar-lev-bassi-2026", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John really likes to write phonology papers. Every day, he either works on some of them or all of them. He is in a cheerful mood now, so apparently... he worked on ALL of his phonology papers today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("he worked on all of his phonology papers today.", .unacceptable)]
    readings := []
    paperFeatures := [("stress", "quantifier")] }

def ex_39a : Datum :=
  { id := "barlevbassi2026_39a"
    source := ⟨"bar-lev-bassi-2026", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John really likes to write phonology papers. He also writes semantics papers, but he hates that. Every day, he either works on all of his phonology papers and none of his semantics papers, or all of his semantics papers and some of his phonology papers. He is in a cheerful mood, so apparently... he worked on his PHONOLOGY papers today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "lexical"), ("counterpart", "barlevbassi2026_39b")] }

def ex_39b : Datum :=
  { id := "barlevbassi2026_39b"
    source := ⟨"bar-lev-bassi-2026", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John really likes to write phonology papers. He also writes semantics papers, but he hates that. Every day, he either works on all of his phonology papers and none of his semantics papers, or all of his semantics papers and some of his phonology papers. He is in a cheerful mood, so apparently... he worked on all of his PHONOLOGY papers today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "lexical")] }

def ex_41a : Datum :=
  { id := "barlevbassi2026_41a"
    source := ⟨"bar-lev-bassi-2026", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not married to his teammates."
    glossedTokens := []
    context := "A monogamous society."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_41b")] }

def ex_41b : Datum :=
  { id := "barlevbassi2026_41b"
    source := ⟨"bar-lev-bassi-2026", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not married to any of his teammates."
    glossedTokens := []
    context := "A monogamous society."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_42a : Datum :=
  { id := "barlevbassi2026_42a"
    source := ⟨"bar-lev-bassi-2026", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I checked in during round three and my uncles were still in the game."
    glossedTokens := []
    context := "In a game of Knuckle, at the end of each round, the person who has more cards than anybody else cashes in and leaves the game. If at the end of a round no player has more cards than anybody else, then all the players stay in the game. Last Saturday night, 5 of my uncles sat down for a long game of Knuckle."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("counterpart", "barlevbassi2026_42b")] }

def ex_42b : Datum :=
  { id := "barlevbassi2026_42b"
    source := ⟨"bar-lev-bassi-2026", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I checked in during round three and all my uncles were still in the game."
    glossedTokens := []
    context := "In a game of Knuckle, at the end of each round, the person who has more cards than anybody else cashes in and leaves the game. If at the end of a round no player has more cards than anybody else, then all the players stay in the game. Last Saturday night, 5 of my uncles sat down for a long game of Knuckle."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_44b : Datum :=
  { id := "barlevbassi2026_44b"
    source := ⟨"bar-lev-bassi-2026", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did she read any of the books? She read the books."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_45a : Datum :=
  { id := "barlevbassi2026_45a"
    source := ⟨"bar-lev-bassi-2026", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mayor is friends with some of the people building the highway, but... she's not MARRIED to those people (so it may not look good but it's not illegal)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "lexical")] }

def fn18_i : Datum :=
  { id := "barlevbassi2026_fn18_i"
    source := ⟨"bar-lev-bassi-2026", "fn. 18 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Is she married to any of her teammates? A: No, she is NOT married to her teammates."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("stress", "polarity")] }

def all : List Datum := [ex_3a, ex_3b, ex_9a, ex_9b, ex_11b, ex_13b_i, ex_13b_ii, ex_15, ex_16, ex_17B, ex_17Bprime, ex_21b_ii, ex_22b, ex_23Bprime, ex_37, ex_37_all, ex_38a, ex_38b, ex_39a, ex_39b, ex_41a, ex_41b, ex_42a, ex_42b, ex_44b, ex_45a, fn18_i]

/-- The constituent bearing the focal stress the paper prints in capitals. -/
inductive Stress where
  /-- quantifier: an overt quantifier, *ALL*, *ANY* -/
  | quantifier
  /-- polarity: the auxiliary or negation realizing the polarity head, *DID*, *NOT* -/
  | polarity
  /-- lexical: another overt word, *PHONOLOGY*, *MARRIED* -/
  | lexical
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `stress`. -/
def stress (e : Datum) : Option Stress :=
  e.parse? "stress" [("quantifier", .quantifier), ("polarity", .polarity), ("lexical", .lexical)]

end BarLevBassi2026.Examples
