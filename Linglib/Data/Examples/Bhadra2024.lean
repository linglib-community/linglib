module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Bhadra2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Bhadra2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bhadra2024.Examples`.
-/

@[expose] public section

namespace Bhadra2024.Examples

def ex_12e : Datum :=
  { id := "bhadra2024_12e"
    source := ⟨"bhadra-2024", "(12e)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "unbuild"
    glossedTokens := [("unbuild", "")]
    glossedWords := [⟨['u', 'n', 'b', 'u', 'i', 'l', 'd'], [], [⟨['u', 'n', 'b', 'u', 'i', 'l', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨0, 1, "verb", some "build"⟩]
    paperFeatures := [("affix", "un")] }

def ex_23a : Datum :=
  { id := "bhadra2024_23a"
    source := ⟨"bhadra-2024", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that caused the rope to be knotted up."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("caused", ""), ("the", ""), ("rope", ""), ("to", ""), ("be", ""), ("knotted", ""), ("up", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['k', 'n', 'o', 't', 't', 'e', 'd'], [], [⟨['k', 'n', 'o', 't', 't', 'e', 'd'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "knotted up")] }

def ex_23b : Datum :=
  { id := "bhadra2024_23b"
    source := ⟨"bhadra-2024", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that caused the rope to tear."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("caused", ""), ("the", ""), ("rope", ""), ("to", ""), ("tear", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['t', 'e', 'a', 'r'], [], [⟨['t', 'e', 'a', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "torn")] }

def ex_23c : Datum :=
  { id := "bhadra2024_23c"
    source := ⟨"bhadra-2024", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that caused the rope to break."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("caused", ""), ("the", ""), ("rope", ""), ("to", ""), ("break", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'r', 'e', 'a', 'k'], [], [⟨['b', 'r', 'e', 'a', 'k'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "broken")] }

def ex_23d : Datum :=
  { id := "bhadra2024_23d"
    source := ⟨"bhadra-2024", "(23d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that caused the rope to disintegrate."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("caused", ""), ("the", ""), ("rope", ""), ("to", ""), ("disintegrate", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['d', 'i', 's', 'i', 'n', 't', 'e', 'g', 'r', 'a', 't', 'e'], [], [⟨['d', 'i', 's', 'i', 'n', 't', 'e', 'g', 'r', 'a', 't', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "disintegrated")] }

def ex_23e : Datum :=
  { id := "bhadra2024_23e"
    source := ⟨"bhadra-2024", "(23e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that caused the rope to come loose."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("caused", ""), ("the", ""), ("rope", ""), ("to", ""), ("come", ""), ("loose", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'e'], [], [⟨['c', 'o', 'm', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'o', 's', 'e'], [], [⟨['l', 'o', 'o', 's', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "loose")] }

def ex_23f : Datum :=
  { id := "bhadra2024_23f"
    source := ⟨"bhadra-2024", "(23f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that caused the rope to tighten."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("caused", ""), ("the", ""), ("rope", ""), ("to", ""), ("tighten", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['t', 'i', 'g', 'h', 't', 'e', 'n'], [], [⟨['t', 'i', 'g', 'h', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "tightened")] }

def ex_23g : Datum :=
  { id := "bhadra2024_23g"
    source := ⟨"bhadra-2024", "(23g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John coiled the rope and that allowed the rope to remain undamaged."
    glossedTokens := [("John", ""), ("coiled", ""), ("the", ""), ("rope", ""), ("and", ""), ("that", ""), ("allowed", ""), ("the", ""), ("rope", ""), ("to", ""), ("remain", ""), ("undamaged", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['c', 'o', 'i', 'l', 'e', 'd'], [], [⟨['c', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['a', 'l', 'l', 'o', 'w', 'e', 'd'], [], [⟨['a', 'l', 'l', 'o', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'p', 'e'], [], [⟨['r', 'o', 'p', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['r', 'e', 'm', 'a', 'i', 'n'], [], [⟨['r', 'e', 'm', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['u', 'n', 'd', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['u', 'n', 'd', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "coil"⟩]
    paperFeatures := [("outcome", "undamaged")] }

def ex_37a : Datum :=
  { id := "bhadra2024_37a"
    source := ⟨"bhadra-2024", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John rebuilt the house."
    glossedTokens := [("John", ""), ("rebuilt", ""), ("the", ""), ("house", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['r', 'e', 'b', 'u', 'i', 'l', 't'], [], [⟨['r', 'e', 'b', 'u', 'i', 'l', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['h', 'o', 'u', 's', 'e'], [], [⟨['h', 'o', 'u', 's', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "verb", some "build"⟩]
    paperFeatures := [("affix", "re")] }

def ex_63a : Datum :=
  { id := "bhadra2024_63a"
    source := ⟨"bhadra-2024", "(63a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The engineers built the bridge and that caused it to come into being."
    glossedTokens := [("The", ""), ("engineers", ""), ("built", ""), ("the", ""), ("bridge", ""), ("and", ""), ("that", ""), ("caused", ""), ("it", ""), ("to", ""), ("come", ""), ("into", ""), ("being", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], [⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], none⟩]⟩, ⟨['b', 'u', 'i', 'l', 't'], [], [⟨['b', 'u', 'i', 'l', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'i', 'd', 'g', 'e'], [], [⟨['b', 'r', 'i', 'd', 'g', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'e'], [], [⟨['c', 'o', 'm', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'o'], [], [⟨['i', 'n', 't', 'o'], [], none⟩]⟩, ⟨['b', 'e', 'i', 'n', 'g'], [], [⟨['b', 'e', 'i', 'n', 'g'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "build"⟩]
    paperFeatures := [("outcome", "come into being")] }

def ex_63b : Datum :=
  { id := "bhadra2024_63b"
    source := ⟨"bhadra-2024", "(63b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The engineers built the bridge and that allowed it to remain intact."
    glossedTokens := [("The", ""), ("engineers", ""), ("built", ""), ("the", ""), ("bridge", ""), ("and", ""), ("that", ""), ("allowed", ""), ("it", ""), ("to", ""), ("remain", ""), ("intact", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], [⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], none⟩]⟩, ⟨['b', 'u', 'i', 'l', 't'], [], [⟨['b', 'u', 'i', 'l', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'i', 'd', 'g', 'e'], [], [⟨['b', 'r', 'i', 'd', 'g', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['a', 'l', 'l', 'o', 'w', 'e', 'd'], [], [⟨['a', 'l', 'l', 'o', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['r', 'e', 'm', 'a', 'i', 'n'], [], [⟨['r', 'e', 'm', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['i', 'n', 't', 'a', 'c', 't'], [], [⟨['i', 'n', 't', 'a', 'c', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "build"⟩]
    paperFeatures := [("outcome", "intact")] }

def ex_63c : Datum :=
  { id := "bhadra2024_63c"
    source := ⟨"bhadra-2024", "(63c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The engineers built the bridge and that caused it to suffer damage."
    glossedTokens := [("The", ""), ("engineers", ""), ("built", ""), ("the", ""), ("bridge", ""), ("and", ""), ("that", ""), ("caused", ""), ("it", ""), ("to", ""), ("suffer", ""), ("damage", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], [⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], none⟩]⟩, ⟨['b', 'u', 'i', 'l', 't'], [], [⟨['b', 'u', 'i', 'l', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'i', 'd', 'g', 'e'], [], [⟨['b', 'r', 'i', 'd', 'g', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['s', 'u', 'f', 'f', 'e', 'r'], [], [⟨['s', 'u', 'f', 'f', 'e', 'r'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "build"⟩]
    paperFeatures := [("outcome", "damaged")] }

def ex_63d : Datum :=
  { id := "bhadra2024_63d"
    source := ⟨"bhadra-2024", "(63d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The engineers built the bridge and that caused it to partially come into being."
    glossedTokens := [("The", ""), ("engineers", ""), ("built", ""), ("the", ""), ("bridge", ""), ("and", ""), ("that", ""), ("caused", ""), ("it", ""), ("to", ""), ("partially", ""), ("come", ""), ("into", ""), ("being", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], [⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], none⟩]⟩, ⟨['b', 'u', 'i', 'l', 't'], [], [⟨['b', 'u', 'i', 'l', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'i', 'd', 'g', 'e'], [], [⟨['b', 'r', 'i', 'd', 'g', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['p', 'a', 'r', 't', 'i', 'a', 'l', 'l', 'y'], [], [⟨['p', 'a', 'r', 't', 'i', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'e'], [], [⟨['c', 'o', 'm', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'o'], [], [⟨['i', 'n', 't', 'o'], [], none⟩]⟩, ⟨['b', 'e', 'i', 'n', 'g'], [], [⟨['b', 'e', 'i', 'n', 'g'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "build"⟩]
    paperFeatures := [("outcome", "partially come into being")] }

def ex_63e : Datum :=
  { id := "bhadra2024_63e"
    source := ⟨"bhadra-2024", "(63e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "The engineers built the bridge and that caused it to become unstable."
    glossedTokens := [("The", ""), ("engineers", ""), ("built", ""), ("the", ""), ("bridge", ""), ("and", ""), ("that", ""), ("caused", ""), ("it", ""), ("to", ""), ("become", ""), ("unstable", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], [⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r', 's'], [], none⟩]⟩, ⟨['b', 'u', 'i', 'l', 't'], [], [⟨['b', 'u', 'i', 'l', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'i', 'd', 'g', 'e'], [], [⟨['b', 'r', 'i', 'd', 'g', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e', 'c', 'o', 'm', 'e'], [], [⟨['b', 'e', 'c', 'o', 'm', 'e'], [], none⟩]⟩, ⟨['u', 'n', 's', 't', 'a', 'b', 'l', 'e'], [], [⟨['u', 'n', 's', 't', 'a', 'b', 'l', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "build"⟩]
    paperFeatures := [("outcome", "unstable")] }

def all : List Datum := [ex_12e, ex_23a, ex_23b, ex_23c, ex_23d, ex_23e, ex_23f, ex_23g, ex_37a, ex_63a, ex_63b, ex_63c, ex_63d, ex_63e]

/-- The prefix on the verb of a row that judges a prefixed form. -/
inductive Affix where
  /-- un: reversative *un-* -/
  | un
  /-- re: restitutive *re-* -/
  | re
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `affix`. -/
def affix (e : Datum) : Option Affix :=
  e.parse? "affix" [("un", .un), ("re", .re)]

/-- The state of the object that a row of the lexical causation test names as brought about by the action. -/
inductive Outcome where
  /-- knotted up: the rope is knotted up -/
  | knottedUp
  /-- torn: the rope is torn -/
  | torn
  /-- broken: the rope is broken -/
  | broken
  /-- disintegrated: the rope has disintegrated -/
  | disintegrated
  /-- loose: the rope has come loose -/
  | loose
  /-- tightened: the rope has tightened -/
  | tightened
  /-- undamaged: the rope remains undamaged -/
  | undamaged
  /-- come into being: the bridge has come into being -/
  | comeIntoBeing
  /-- intact: the bridge remains intact -/
  | intact
  /-- damaged: the bridge has suffered damage -/
  | damaged
  /-- partially come into being: the bridge has partially come into being -/
  | partiallyComeIntoBeing
  /-- unstable: the bridge has become unstable -/
  | unstable
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `outcome`. -/
def outcome (e : Datum) : Option Outcome :=
  e.parse? "outcome" [("knotted up", .knottedUp), ("torn", .torn), ("broken", .broken),
    ("disintegrated", .disintegrated), ("loose", .loose), ("tightened", .tightened),
    ("undamaged", .undamaged), ("come into being", .comeIntoBeing), ("intact", .intact),
    ("damaged", .damaged), ("partially come into being", .partiallyComeIntoBeing),
    ("unstable", .unstable)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- verb: the verb under test, or the base of the prefixed verb -/
  | verb
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("verb", .verb)]

/-- The verbs under test. -/
inductive Lexeme where
  /-- coil: the English verb *coil* -/
  | coil
  /-- build: the English verb *build* -/
  | build
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("coil", .coil), ("build", .build)])

end Bhadra2024.Examples
