module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `MartinRoseNichols2025` — typed example data

Auto-generated from `Linglib/Data/Examples/MartinRoseNichols2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MartinRoseNichols2025.Examples`.
-/

@[expose] public section

namespace MartinRoseNichols2025.Examples

def ex_5a : Datum :=
  { id := "martinrosenichols2025_5a"
    source := ⟨"martin-rose-nichols-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of sunscreen caused Jane's skin to burn."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("sunscreen", ""), ("caused", ""), ("Jane's", ""), ("skin", ""), ("to", ""), ("burn", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], [⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e', '\'', 's'], [], [⟨['J', 'a', 'n', 'e', '\'', 's'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "absence")] }

def ex_5b : Datum :=
  { id := "martinrosenichols2025_5b"
    source := ⟨"martin-rose-nichols-2025", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of sunscreen burned Jane's skin."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("sunscreen", ""), ("burned", ""), ("Jane's", ""), ("skin", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], [⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e', '\'', 's'], [], [⟨['J', 'a', 'n', 'e', '\'', 's'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_6a : Datum :=
  { id := "martinrosenichols2025_6a"
    source := ⟨"martin-rose-nichols-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of a heat shield caused the rubber gasket to melt."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("a", ""), ("heat", ""), ("shield", ""), ("caused", ""), ("the", ""), ("rubber", ""), ("gasket", ""), ("to", ""), ("melt", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't'], [], [⟨['h', 'e', 'a', 't'], [], none⟩]⟩, ⟨['s', 'h', 'i', 'e', 'l', 'd'], [], [⟨['s', 'h', 'i', 'e', 'l', 'd'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'u', 'b', 'b', 'e', 'r'], [], [⟨['r', 'u', 'b', 'b', 'e', 'r'], [], none⟩]⟩, ⟨['g', 'a', 's', 'k', 'e', 't'], [], [⟨['g', 'a', 's', 'k', 'e', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't'], [], [⟨['m', 'e', 'l', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "absence")] }

def ex_6b : Datum :=
  { id := "martinrosenichols2025_6b"
    source := ⟨"martin-rose-nichols-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of a heat shield melted the rubber gasket."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("a", ""), ("heat", ""), ("shield", ""), ("melted", ""), ("the", ""), ("rubber", ""), ("gasket", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't'], [], [⟨['h', 'e', 'a', 't'], [], none⟩]⟩, ⟨['s', 'h', 'i', 'e', 'l', 'd'], [], [⟨['s', 'h', 'i', 'e', 'l', 'd'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'u', 'b', 'b', 'e', 'r'], [], [⟨['r', 'u', 'b', 'b', 'e', 'r'], [], none⟩]⟩, ⟨['g', 'a', 's', 'k', 'e', 't'], [], [⟨['g', 'a', 's', 'k', 'e', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_7a : Datum :=
  { id := "martinrosenichols2025_7a"
    source := ⟨"martin-rose-nichols-2025", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of a basement window caused the cellar to flood."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("a", ""), ("basement", ""), ("window", ""), ("caused", ""), ("the", ""), ("cellar", ""), ("to", ""), ("flood", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], [⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'n', 'd', 'o', 'w'], [], [⟨['w', 'i', 'n', 'd', 'o', 'w'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'e', 'l', 'l', 'a', 'r'], [], [⟨['c', 'e', 'l', 'l', 'a', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "absence")] }

def ex_7b : Datum :=
  { id := "martinrosenichols2025_7b"
    source := ⟨"martin-rose-nichols-2025", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of a basement window flooded the cellar."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("a", ""), ("basement", ""), ("window", ""), ("flooded", ""), ("the", ""), ("cellar", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], [⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩, ⟨['w', 'i', 'n', 'd', 'o', 'w'], [], [⟨['w', 'i', 'n', 'd', 'o', 'w'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'e', 'l', 'l', 'a', 'r'], [], [⟨['c', 'e', 'l', 'l', 'a', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_9a : Datum :=
  { id := "martinrosenichols2025_9a"
    source := ⟨"martin-rose-nichols-2025", "(9a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "De Rossi's complete lack of discipline burned this team."
    glossedTokens := [("De", ""), ("Rossi's", ""), ("complete", ""), ("lack", ""), ("of", ""), ("discipline", ""), ("burned", ""), ("this", ""), ("team", "")]
    glossedWords := [⟨['D', 'e'], [], [⟨['D', 'e'], [], none⟩]⟩, ⟨['R', 'o', 's', 's', 'i', '\'', 's'], [], [⟨['R', 'o', 's', 's', 'i', '\'', 's'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'l', 'e', 't', 'e'], [], [⟨['c', 'o', 'm', 'p', 'l', 'e', 't', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['d', 'i', 's', 'c', 'i', 'p', 'l', 'i', 'n', 'e'], [], [⟨['d', 'i', 's', 'c', 'i', 'p', 'l', 'i', 'n', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'i', 's'], [], [⟨['t', 'h', 'i', 's'], [], none⟩]⟩, ⟨['t', 'e', 'a', 'm'], [], [⟨['t', 'e', 'a', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "absence")] }

def ex_9b : Datum :=
  { id := "martinrosenichols2025_9b"
    source := ⟨"martin-rose-nichols-2025", "(9b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "His utter lack of egotism melted me completely."
    glossedTokens := [("His", ""), ("utter", ""), ("lack", ""), ("of", ""), ("egotism", ""), ("melted", ""), ("me", ""), ("completely", "")]
    glossedWords := [⟨['H', 'i', 's'], [], [⟨['H', 'i', 's'], [], none⟩]⟩, ⟨['u', 't', 't', 'e', 'r'], [], [⟨['u', 't', 't', 'e', 'r'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['e', 'g', 'o', 't', 'i', 's', 'm'], [], [⟨['e', 'g', 'o', 't', 'i', 's', 'm'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'e'], [], [⟨['m', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', 'l', 'y'], [], [⟨['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "absence")] }

def ex_9c : Datum :=
  { id := "martinrosenichols2025_9c"
    source := ⟨"martin-rose-nichols-2025", "(9c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The lack of colour flooded his thoughts."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("colour", ""), ("flooded", ""), ("his", ""), ("thoughts", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['c', 'o', 'l', 'o', 'u', 'r'], [], [⟨['c', 'o', 'l', 'o', 'u', 'r'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['t', 'h', 'o', 'u', 'g', 'h', 't', 's'], [], [⟨['t', 'h', 'o', 'u', 'g', 'h', 't', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "absence")] }

def ex_10a : Datum :=
  { id := "martinrosenichols2025_10a"
    source := ⟨"martin-rose-nichols-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of water killed my plants."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("water", ""), ("killed", ""), ("my", ""), ("plants", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], [], [⟨['w', 'a', 't', 'e', 'r'], [], none⟩]⟩, ⟨['k', 'i', 'l', 'l', 'e', 'd'], [], [⟨['k', 'i', 'l', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['p', 'l', 'a', 'n', 't', 's'], [], [⟨['p', 'l', 'a', 'n', 't', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "kill"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_10b : Datum :=
  { id := "martinrosenichols2025_10b"
    source := ⟨"martin-rose-nichols-2025", "(10b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Lack of oxygen damaged her brain."
    glossedTokens := [("Lack", ""), ("of", ""), ("oxygen", ""), ("damaged", ""), ("her", ""), ("brain", "")]
    glossedWords := [⟨['L', 'a', 'c', 'k'], [], [⟨['L', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['o', 'x', 'y', 'g', 'e', 'n'], [], [⟨['o', 'x', 'y', 'g', 'e', 'n'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['b', 'r', 'a', 'i', 'n'], [], [⟨['b', 'r', 'a', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_10c : Datum :=
  { id := "martinrosenichols2025_10c"
    source := ⟨"martin-rose-nichols-2025", "(10c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A lack of supplies triggered a great famine."
    glossedTokens := [("A", ""), ("lack", ""), ("of", ""), ("supplies", ""), ("triggered", ""), ("a", ""), ("great", ""), ("famine", "")]
    glossedWords := [⟨['A'], [], [⟨['A'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['s', 'u', 'p', 'p', 'l', 'i', 'e', 's'], [], [⟨['s', 'u', 'p', 'p', 'l', 'i', 'e', 's'], [], none⟩]⟩, ⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], [⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['g', 'r', 'e', 'a', 't'], [], [⟨['g', 'r', 'e', 'a', 't'], [], none⟩]⟩, ⟨['f', 'a', 'm', 'i', 'n', 'e'], [], [⟨['f', 'a', 'm', 'i', 'n', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "trigger"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_12a : Datum :=
  { id := "martinrosenichols2025_12a"
    source := ⟨"martin-rose-nichols-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of vitamins changed Jane's skin."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("vitamins", ""), ("changed", ""), ("Jane's", ""), ("skin", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['v', 'i', 't', 'a', 'm', 'i', 'n', 's'], [], [⟨['v', 'i', 't', 'a', 'm', 'i', 'n', 's'], [], none⟩]⟩, ⟨['c', 'h', 'a', 'n', 'g', 'e', 'd'], [], [⟨['c', 'h', 'a', 'n', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e', '\'', 's'], [], [⟨['J', 'a', 'n', 'e', '\'', 's'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "change"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_12b : Datum :=
  { id := "martinrosenichols2025_12b"
    source := ⟨"martin-rose-nichols-2025", "(12b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The lack of XBP1 activated the other protein."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("XBP1", ""), ("activated", ""), ("the", ""), ("other", ""), ("protein", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['X', 'B', 'P', '1'], [], [⟨['X', 'B', 'P', '1'], [], none⟩]⟩, ⟨['a', 'c', 't', 'i', 'v', 'a', 't', 'e', 'd'], [], [⟨['a', 'c', 't', 'i', 'v', 'a', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['o', 't', 'h', 'e', 'r'], [], [⟨['o', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'r', 'o', 't', 'e', 'i', 'n'], [], [⟨['p', 'r', 'o', 't', 'e', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "activate"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_13a : Datum :=
  { id := "martinrosenichols2025_13a"
    source := ⟨"martin-rose-nichols-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of drainage buried the road."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("drainage", ""), ("buried", ""), ("the", ""), ("road", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], [⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'i', 'e', 'd'], [], [⟨['b', 'u', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'a', 'd'], [], [⟨['r', 'o', 'a', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "bury"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_13b : Datum :=
  { id := "martinrosenichols2025_13b"
    source := ⟨"martin-rose-nichols-2025", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of drainage caused the road to be buried."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("drainage", ""), ("caused", ""), ("the", ""), ("road", ""), ("to", ""), ("be", ""), ("buried", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], [⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'o', 'a', 'd'], [], [⟨['r', 'o', 'a', 'd'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'i', 'e', 'd'], [], [⟨['b', 'u', 'r', 'i', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "verb", some "bury"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "absence")] }

def ex_13c : Datum :=
  { id := "martinrosenichols2025_13c"
    source := ⟨"martin-rose-nichols-2025", "(13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of funding buried the project."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("funding", ""), ("buried", ""), ("the", ""), ("project", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['f', 'u', 'n', 'd', 'i', 'n', 'g'], [], [⟨['f', 'u', 'n', 'd', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'i', 'e', 'd'], [], [⟨['b', 'u', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'r', 'o', 'j', 'e', 'c', 't'], [], [⟨['p', 'r', 'o', 'j', 'e', 'c', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "bury"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "absence")] }

def ex_14a : Datum :=
  { id := "martinrosenichols2025_14a"
    source := ⟨"martin-rose-nichols-2025", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My skin burned from the lack of sunscreen."
    glossedTokens := [("My", ""), ("skin", ""), ("burned", ""), ("from", ""), ("the", ""), ("lack", ""), ("of", ""), ("sunscreen", "")]
    glossedWords := [⟨['M', 'y'], [], [⟨['M', 'y'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], [⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "anticausative"), ("sense", "physical"), ("subject", "absence")] }

def ex_14b : Datum :=
  { id := "martinrosenichols2025_14b"
    source := ⟨"martin-rose-nichols-2025", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of sunscreen burned my skin."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("sunscreen", ""), ("burned", ""), ("my", ""), ("skin", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], [⟨['s', 'u', 'n', 's', 'c', 'r', 'e', 'e', 'n'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_15a : Datum :=
  { id := "martinrosenichols2025_15a"
    source := ⟨"martin-rose-nichols-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase broke from a lack of proper packing."
    glossedTokens := [("The", ""), ("vase", ""), ("broke", ""), ("from", ""), ("a", ""), ("lack", ""), ("of", ""), ("proper", ""), ("packing", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['v', 'a', 's', 'e'], [], [⟨['v', 'a', 's', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'o', 'k', 'e'], [], [⟨['b', 'r', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['p', 'r', 'o', 'p', 'e', 'r'], [], [⟨['p', 'r', 'o', 'p', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 'c', 'k', 'i', 'n', 'g'], [], [⟨['p', 'a', 'c', 'k', 'i', 'n', 'g'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "break"⟩]
    paperFeatures := [("frame", "anticausative"), ("sense", "physical"), ("subject", "absence")] }

def ex_15b : Datum :=
  { id := "martinrosenichols2025_15b"
    source := ⟨"martin-rose-nichols-2025", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of proper packing broke the vase."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("proper", ""), ("packing", ""), ("broke", ""), ("the", ""), ("vase", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['p', 'r', 'o', 'p', 'e', 'r'], [], [⟨['p', 'r', 'o', 'p', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 'c', 'k', 'i', 'n', 'g'], [], [⟨['p', 'a', 'c', 'k', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['b', 'r', 'o', 'k', 'e'], [], [⟨['b', 'r', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['v', 'a', 's', 'e'], [], [⟨['v', 'a', 's', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "break"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_16a : Datum :=
  { id := "martinrosenichols2025_16a"
    source := ⟨"martin-rose-nichols-2025", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pistons cracked from a lack of proper lubrication."
    glossedTokens := [("The", ""), ("pistons", ""), ("cracked", ""), ("from", ""), ("a", ""), ("lack", ""), ("of", ""), ("proper", ""), ("lubrication", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'i', 's', 't', 'o', 'n', 's'], [], [⟨['p', 'i', 's', 't', 'o', 'n', 's'], [], none⟩]⟩, ⟨['c', 'r', 'a', 'c', 'k', 'e', 'd'], [], [⟨['c', 'r', 'a', 'c', 'k', 'e', 'd'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['p', 'r', 'o', 'p', 'e', 'r'], [], [⟨['p', 'r', 'o', 'p', 'e', 'r'], [], none⟩]⟩, ⟨['l', 'u', 'b', 'r', 'i', 'c', 'a', 't', 'i', 'o', 'n'], [], [⟨['l', 'u', 'b', 'r', 'i', 'c', 'a', 't', 'i', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "crack"⟩]
    paperFeatures := [("frame", "anticausative"), ("sense", "physical"), ("subject", "absence")] }

def ex_16b : Datum :=
  { id := "martinrosenichols2025_16b"
    source := ⟨"martin-rose-nichols-2025", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lack of proper lubrication cracked the pistons."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("proper", ""), ("lubrication", ""), ("cracked", ""), ("the", ""), ("pistons", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['p', 'r', 'o', 'p', 'e', 'r'], [], [⟨['p', 'r', 'o', 'p', 'e', 'r'], [], none⟩]⟩, ⟨['l', 'u', 'b', 'r', 'i', 'c', 'a', 't', 'i', 'o', 'n'], [], [⟨['l', 'u', 'b', 'r', 'i', 'c', 'a', 't', 'i', 'o', 'n'], [], none⟩]⟩, ⟨['c', 'r', 'a', 'c', 'k', 'e', 'd'], [], [⟨['c', 'r', 'a', 'c', 'k', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'i', 's', 't', 'o', 'n', 's'], [], [⟨['p', 'i', 's', 't', 'o', 'n', 's'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "crack"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_18a_damage : Datum :=
  { id := "martinrosenichols2025_18a_damage"
    source := ⟨"martin-rose-nichols-2025", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Andy left the phone on the table caused it to be damaged."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Andy", ""), ("left", ""), ("the", ""), ("phone", ""), ("on", ""), ("the", ""), ("table", ""), ("caused", ""), ("it", ""), ("to", ""), ("be", ""), ("damaged", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['A', 'n', 'd', 'y'], [], [⟨['A', 'n', 'd', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e'], [], [⟨['t', 'a', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨14, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "fact")] }

def ex_18a_burn : Datum :=
  { id := "martinrosenichols2025_18a_burn"
    source := ⟨"martin-rose-nichols-2025", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Andy left the phone on the table caused it to burn."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Andy", ""), ("left", ""), ("the", ""), ("phone", ""), ("on", ""), ("the", ""), ("table", ""), ("caused", ""), ("it", ""), ("to", ""), ("burn", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['A', 'n', 'd', 'y'], [], [⟨['A', 'n', 'd', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e'], [], [⟨['t', 'a', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨13, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "fact")] }

def ex_18b_damage : Datum :=
  { id := "martinrosenichols2025_18b_damage"
    source := ⟨"martin-rose-nichols-2025", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Andy left the phone on the table damaged it."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Andy", ""), ("left", ""), ("the", ""), ("phone", ""), ("on", ""), ("the", ""), ("table", ""), ("damaged", ""), ("it", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['A', 'n', 'd', 'y'], [], [⟨['A', 'n', 'd', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e'], [], [⟨['t', 'a', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "fact")] }

def ex_18b_burn : Datum :=
  { id := "martinrosenichols2025_18b_burn"
    source := ⟨"martin-rose-nichols-2025", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Andy left the phone on the table burned it."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Andy", ""), ("left", ""), ("the", ""), ("phone", ""), ("on", ""), ("the", ""), ("table", ""), ("burned", ""), ("it", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['A', 'n', 'd', 'y'], [], [⟨['A', 'n', 'd', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e'], [], [⟨['t', 'a', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "fact")] }

def ex_19a_destroy : Datum :=
  { id := "martinrosenichols2025_19a_destroy"
    source := ⟨"martin-rose-nichols-2025", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Lee heated his lunchbox with its cover in the microwave caused the plastic to be destroyed."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Lee", ""), ("heated", ""), ("his", ""), ("lunchbox", ""), ("with", ""), ("its", ""), ("cover", ""), ("in", ""), ("the", ""), ("microwave", ""), ("caused", ""), ("the", ""), ("plastic", ""), ("to", ""), ("be", ""), ("destroyed", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['L', 'e', 'e'], [], [⟨['L', 'e', 'e'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'e', 'd'], [], [⟨['h', 'e', 'a', 't', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], [⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['i', 't', 's'], [], [⟨['i', 't', 's'], [], none⟩]⟩, ⟨['c', 'o', 'v', 'e', 'r'], [], [⟨['c', 'o', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], [⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], [⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨18, 1, "verb", some "destroy"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "fact")] }

def ex_19a_melt : Datum :=
  { id := "martinrosenichols2025_19a_melt"
    source := ⟨"martin-rose-nichols-2025", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Lee heated his lunchbox with its cover in the microwave caused the plastic to melt."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Lee", ""), ("heated", ""), ("his", ""), ("lunchbox", ""), ("with", ""), ("its", ""), ("cover", ""), ("in", ""), ("the", ""), ("microwave", ""), ("caused", ""), ("the", ""), ("plastic", ""), ("to", ""), ("melt", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['L', 'e', 'e'], [], [⟨['L', 'e', 'e'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'e', 'd'], [], [⟨['h', 'e', 'a', 't', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], [⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['i', 't', 's'], [], [⟨['i', 't', 's'], [], none⟩]⟩, ⟨['c', 'o', 'v', 'e', 'r'], [], [⟨['c', 'o', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], [⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't'], [], [⟨['m', 'e', 'l', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨17, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "fact")] }

def ex_19b_destroy : Datum :=
  { id := "martinrosenichols2025_19b_destroy"
    source := ⟨"martin-rose-nichols-2025", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Lee heated his lunchbox with its cover in the microwave destroyed the plastic."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Lee", ""), ("heated", ""), ("his", ""), ("lunchbox", ""), ("with", ""), ("its", ""), ("cover", ""), ("in", ""), ("the", ""), ("microwave", ""), ("destroyed", ""), ("the", ""), ("plastic", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['L', 'e', 'e'], [], [⟨['L', 'e', 'e'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'e', 'd'], [], [⟨['h', 'e', 'a', 't', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], [⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['i', 't', 's'], [], [⟨['i', 't', 's'], [], none⟩]⟩, ⟨['c', 'o', 'v', 'e', 'r'], [], [⟨['c', 'o', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], [⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], [⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨13, 1, "verb", some "destroy"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "fact")] }

def ex_19b_melt : Datum :=
  { id := "martinrosenichols2025_19b_melt"
    source := ⟨"martin-rose-nichols-2025", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that Lee heated his lunchbox with its cover in the microwave melted the plastic."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("Lee", ""), ("heated", ""), ("his", ""), ("lunchbox", ""), ("with", ""), ("its", ""), ("cover", ""), ("in", ""), ("the", ""), ("microwave", ""), ("melted", ""), ("the", ""), ("plastic", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['L', 'e', 'e'], [], [⟨['L', 'e', 'e'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'e', 'd'], [], [⟨['h', 'e', 'a', 't', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], [⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['i', 't', 's'], [], [⟨['i', 't', 's'], [], none⟩]⟩, ⟨['c', 'o', 'v', 'e', 'r'], [], [⟨['c', 'o', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], [⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨13, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "fact")] }

def ex_21a : Datum :=
  { id := "martinrosenichols2025_21a"
    source := ⟨"martin-rose-nichols-2025", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Andy's leaving the phone on the table caused it to burn."
    glossedTokens := [("Andy's", ""), ("leaving", ""), ("the", ""), ("phone", ""), ("on", ""), ("the", ""), ("table", ""), ("caused", ""), ("it", ""), ("to", ""), ("burn", "")]
    glossedWords := [⟨['A', 'n', 'd', 'y', '\'', 's'], [], [⟨['A', 'n', 'd', 'y', '\'', 's'], [], none⟩]⟩, ⟨['l', 'e', 'a', 'v', 'i', 'n', 'g'], [], [⟨['l', 'e', 'a', 'v', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e'], [], [⟨['t', 'a', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "gerund")] }

def ex_21b : Datum :=
  { id := "martinrosenichols2025_21b"
    source := ⟨"martin-rose-nichols-2025", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Andy's leaving his phone on the table burned it."
    glossedTokens := [("Andy's", ""), ("leaving", ""), ("his", ""), ("phone", ""), ("on", ""), ("the", ""), ("table", ""), ("burned", ""), ("it", "")]
    glossedWords := [⟨['A', 'n', 'd', 'y', '\'', 's'], [], [⟨['A', 'n', 'd', 'y', '\'', 's'], [], none⟩]⟩, ⟨['l', 'e', 'a', 'v', 'i', 'n', 'g'], [], [⟨['l', 'e', 'a', 'v', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'a', 'b', 'l', 'e'], [], [⟨['t', 'a', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "gerund")] }

def ex_22a : Datum :=
  { id := "martinrosenichols2025_22a"
    source := ⟨"martin-rose-nichols-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lee's heating his lunchbox with its cover in the microwave caused the plastic to melt."
    glossedTokens := [("Lee's", ""), ("heating", ""), ("his", ""), ("lunchbox", ""), ("with", ""), ("its", ""), ("cover", ""), ("in", ""), ("the", ""), ("microwave", ""), ("caused", ""), ("the", ""), ("plastic", ""), ("to", ""), ("melt", "")]
    glossedWords := [⟨['L', 'e', 'e', '\'', 's'], [], [⟨['L', 'e', 'e', '\'', 's'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'i', 'n', 'g'], [], [⟨['h', 'e', 'a', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], [⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['i', 't', 's'], [], [⟨['i', 't', 's'], [], none⟩]⟩, ⟨['c', 'o', 'v', 'e', 'r'], [], [⟨['c', 'o', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], [⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't'], [], [⟨['m', 'e', 'l', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨14, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "gerund")] }

def ex_22b : Datum :=
  { id := "martinrosenichols2025_22b"
    source := ⟨"martin-rose-nichols-2025", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lee's heating his lunchbox with its cover in the microwave melted the plastic."
    glossedTokens := [("Lee's", ""), ("heating", ""), ("his", ""), ("lunchbox", ""), ("with", ""), ("its", ""), ("cover", ""), ("in", ""), ("the", ""), ("microwave", ""), ("melted", ""), ("the", ""), ("plastic", "")]
    glossedWords := [⟨['L', 'e', 'e', '\'', 's'], [], [⟨['L', 'e', 'e', '\'', 's'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'i', 'n', 'g'], [], [⟨['h', 'e', 'a', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], [⟨['l', 'u', 'n', 'c', 'h', 'b', 'o', 'x'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['i', 't', 's'], [], [⟨['i', 't', 's'], [], none⟩]⟩, ⟨['c', 'o', 'v', 'e', 'r'], [], [⟨['c', 'o', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], [⟨['m', 'i', 'c', 'r', 'o', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "gerund")] }

def ex_23a : Datum :=
  { id := "martinrosenichols2025_23a"
    source := ⟨"martin-rose-nichols-2025", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's blocking the drainage system caused the basement to flood."
    glossedTokens := [("John's", ""), ("blocking", ""), ("the", ""), ("drainage", ""), ("system", ""), ("caused", ""), ("the", ""), ("basement", ""), ("to", ""), ("flood", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '\'', 's'], [], [⟨['J', 'o', 'h', 'n', '\'', 's'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], [⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], [⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['s', 'y', 's', 't', 'e', 'm'], [], [⟨['s', 'y', 's', 't', 'e', 'm'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], [⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "gerund")] }

def ex_23b : Datum :=
  { id := "martinrosenichols2025_23b"
    source := ⟨"martin-rose-nichols-2025", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's blocking the drainage system flooded the basement."
    glossedTokens := [("John's", ""), ("blocking", ""), ("the", ""), ("drainage", ""), ("system", ""), ("flooded", ""), ("the", ""), ("basement", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '\'', 's'], [], [⟨['J', 'o', 'h', 'n', '\'', 's'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], [⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], [⟨['d', 'r', 'a', 'i', 'n', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['s', 'y', 's', 't', 'e', 'm'], [], [⟨['s', 'y', 's', 't', 'e', 'm'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], [⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "gerund")] }

def ex_24a : Datum :=
  { id := "martinrosenichols2025_24a"
    source := ⟨"martin-rose-nichols-2025", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom's telling that story during the interview burned his chances at that job."
    glossedTokens := [("Tom's", ""), ("telling", ""), ("that", ""), ("story", ""), ("during", ""), ("the", ""), ("interview", ""), ("burned", ""), ("his", ""), ("chances", ""), ("at", ""), ("that", ""), ("job", "")]
    glossedWords := [⟨['T', 'o', 'm', '\'', 's'], [], [⟨['T', 'o', 'm', '\'', 's'], [], none⟩]⟩, ⟨['t', 'e', 'l', 'l', 'i', 'n', 'g'], [], [⟨['t', 'e', 'l', 'l', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['s', 't', 'o', 'r', 'y'], [], [⟨['s', 't', 'o', 'r', 'y'], [], none⟩]⟩, ⟨['d', 'u', 'r', 'i', 'n', 'g'], [], [⟨['d', 'u', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'r', 'v', 'i', 'e', 'w'], [], [⟨['i', 'n', 't', 'e', 'r', 'v', 'i', 'e', 'w'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['c', 'h', 'a', 'n', 'c', 'e', 's'], [], [⟨['c', 'h', 'a', 'n', 'c', 'e', 's'], [], none⟩]⟩, ⟨['a', 't'], [], [⟨['a', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['j', 'o', 'b'], [], [⟨['j', 'o', 'b'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "gerund")] }

def ex_24b : Datum :=
  { id := "martinrosenichols2025_24b"
    source := ⟨"martin-rose-nichols-2025", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Iran's accepting the principle of a cease-fire melted their resistance to the idea."
    glossedTokens := [("Iran's", ""), ("accepting", ""), ("the", ""), ("principle", ""), ("of", ""), ("a", ""), ("cease-fire", ""), ("melted", ""), ("their", ""), ("resistance", ""), ("to", ""), ("the", ""), ("idea", "")]
    glossedWords := [⟨['I', 'r', 'a', 'n', '\'', 's'], [], [⟨['I', 'r', 'a', 'n', '\'', 's'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'e', 'p', 't', 'i', 'n', 'g'], [], [⟨['a', 'c', 'c', 'e', 'p', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'r', 'i', 'n', 'c', 'i', 'p', 'l', 'e'], [], [⟨['p', 'r', 'i', 'n', 'c', 'i', 'p', 'l', 'e'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['c', 'e', 'a', 's', 'e', '-', 'f', 'i', 'r', 'e'], [], [⟨['c', 'e', 'a', 's', 'e'], [], none⟩, ⟨['f', 'i', 'r', 'e'], [], some '-'⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'i', 'r'], [], [⟨['t', 'h', 'e', 'i', 'r'], [], none⟩]⟩, ⟨['r', 'e', 's', 'i', 's', 't', 'a', 'n', 'c', 'e'], [], [⟨['r', 'e', 's', 'i', 's', 't', 'a', 'n', 'c', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'd', 'e', 'a'], [], [⟨['i', 'd', 'e', 'a'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "gerund")] }

def ex_24c : Datum :=
  { id := "martinrosenichols2025_24c"
    source := ⟨"martin-rose-nichols-2025", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Callas' singing Casta Diva flooded me with emotions."
    glossedTokens := [("Callas'", ""), ("singing", ""), ("Casta", ""), ("Diva", ""), ("flooded", ""), ("me", ""), ("with", ""), ("emotions", "")]
    glossedWords := [⟨['C', 'a', 'l', 'l', 'a', 's', '\''], [], [⟨['C', 'a', 'l', 'l', 'a', 's', '\''], [], none⟩]⟩, ⟨['s', 'i', 'n', 'g', 'i', 'n', 'g'], [], [⟨['s', 'i', 'n', 'g', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['C', 'a', 's', 't', 'a'], [], [⟨['C', 'a', 's', 't', 'a'], [], none⟩]⟩, ⟨['D', 'i', 'v', 'a'], [], [⟨['D', 'i', 'v', 'a'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'e'], [], [⟨['m', 'e'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['e', 'm', 'o', 't', 'i', 'o', 'n', 's'], [], [⟨['e', 'm', 'o', 't', 'i', 'o', 'n', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "gerund")] }

def ex_25a : Datum :=
  { id := "martinrosenichols2025_25a"
    source := ⟨"martin-rose-nichols-2025", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josh's plugging the socket in the wrong voltage caused it to be damaged."
    glossedTokens := [("Josh's", ""), ("plugging", ""), ("the", ""), ("socket", ""), ("in", ""), ("the", ""), ("wrong", ""), ("voltage", ""), ("caused", ""), ("it", ""), ("to", ""), ("be", ""), ("damaged", "")]
    glossedWords := [⟨['J', 'o', 's', 'h', '\'', 's'], [], [⟨['J', 'o', 's', 'h', '\'', 's'], [], none⟩]⟩, ⟨['p', 'l', 'u', 'g', 'g', 'i', 'n', 'g'], [], [⟨['p', 'l', 'u', 'g', 'g', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'o', 'c', 'k', 'e', 't'], [], [⟨['s', 'o', 'c', 'k', 'e', 't'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'r', 'o', 'n', 'g'], [], [⟨['w', 'r', 'o', 'n', 'g'], [], none⟩]⟩, ⟨['v', 'o', 'l', 't', 'a', 'g', 'e'], [], [⟨['v', 'o', 'l', 't', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨12, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "gerund")] }

def ex_25b : Datum :=
  { id := "martinrosenichols2025_25b"
    source := ⟨"martin-rose-nichols-2025", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Josh's plugging the socket in the wrong voltage damaged the computer."
    glossedTokens := [("Josh's", ""), ("plugging", ""), ("the", ""), ("socket", ""), ("in", ""), ("the", ""), ("wrong", ""), ("voltage", ""), ("damaged", ""), ("the", ""), ("computer", "")]
    glossedWords := [⟨['J', 'o', 's', 'h', '\'', 's'], [], [⟨['J', 'o', 's', 'h', '\'', 's'], [], none⟩]⟩, ⟨['p', 'l', 'u', 'g', 'g', 'i', 'n', 'g'], [], [⟨['p', 'l', 'u', 'g', 'g', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'o', 'c', 'k', 'e', 't'], [], [⟨['s', 'o', 'c', 'k', 'e', 't'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'r', 'o', 'n', 'g'], [], [⟨['w', 'r', 'o', 'n', 'g'], [], none⟩]⟩, ⟨['v', 'o', 'l', 't', 'a', 'g', 'e'], [], [⟨['v', 'o', 'l', 't', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], [], [⟨['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "gerund")] }

def ex_26a : Datum :=
  { id := "martinrosenichols2025_26a"
    source := ⟨"martin-rose-nichols-2025", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My neighbor's not watering my plants caused them to die."
    glossedTokens := [("My", ""), ("neighbor's", ""), ("not", ""), ("watering", ""), ("my", ""), ("plants", ""), ("caused", ""), ("them", ""), ("to", ""), ("die", "")]
    glossedWords := [⟨['M', 'y'], [], [⟨['M', 'y'], [], none⟩]⟩, ⟨['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '\'', 's'], [], [⟨['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '\'', 's'], [], none⟩]⟩, ⟨['n', 'o', 't'], [], [⟨['n', 'o', 't'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r', 'i', 'n', 'g'], [], [⟨['w', 'a', 't', 'e', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['p', 'l', 'a', 'n', 't', 's'], [], [⟨['p', 'l', 'a', 'n', 't', 's'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'm'], [], [⟨['t', 'h', 'e', 'm'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['d', 'i', 'e'], [], [⟨['d', 'i', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "verb", some "die"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "gerund")] }

def ex_26b : Datum :=
  { id := "martinrosenichols2025_26b"
    source := ⟨"martin-rose-nichols-2025", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My neighbor's not watering my plants killed them."
    glossedTokens := [("My", ""), ("neighbor's", ""), ("not", ""), ("watering", ""), ("my", ""), ("plants", ""), ("killed", ""), ("them", "")]
    glossedWords := [⟨['M', 'y'], [], [⟨['M', 'y'], [], none⟩]⟩, ⟨['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '\'', 's'], [], [⟨['n', 'e', 'i', 'g', 'h', 'b', 'o', 'r', '\'', 's'], [], none⟩]⟩, ⟨['n', 'o', 't'], [], [⟨['n', 'o', 't'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r', 'i', 'n', 'g'], [], [⟨['w', 'a', 't', 'e', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['p', 'l', 'a', 'n', 't', 's'], [], [⟨['p', 'l', 'a', 'n', 't', 's'], [], none⟩]⟩, ⟨['k', 'i', 'l', 'l', 'e', 'd'], [], [⟨['k', 'i', 'l', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'm'], [], [⟨['t', 'h', 'e', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "kill"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "gerund")] }

def ex_27a : Datum :=
  { id := "martinrosenichols2025_27a"
    source := ⟨"martin-rose-nichols-2025", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Camacho's inspecting the package caused the detonator to be triggered."
    glossedTokens := [("Camacho's", ""), ("inspecting", ""), ("the", ""), ("package", ""), ("caused", ""), ("the", ""), ("detonator", ""), ("to", ""), ("be", ""), ("triggered", "")]
    glossedWords := [⟨['C', 'a', 'm', 'a', 'c', 'h', 'o', '\'', 's'], [], [⟨['C', 'a', 'm', 'a', 'c', 'h', 'o', '\'', 's'], [], none⟩]⟩, ⟨['i', 'n', 's', 'p', 'e', 'c', 't', 'i', 'n', 'g'], [], [⟨['i', 'n', 's', 'p', 'e', 'c', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'a', 'c', 'k', 'a', 'g', 'e'], [], [⟨['p', 'a', 'c', 'k', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'e', 't', 'o', 'n', 'a', 't', 'o', 'r'], [], [⟨['d', 'e', 't', 'o', 'n', 'a', 't', 'o', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], [⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "verb", some "trigger"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "gerund")] }

def ex_27b : Datum :=
  { id := "martinrosenichols2025_27b"
    source := ⟨"martin-rose-nichols-2025", "(27b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Camacho's inspecting the package triggered the detonator."
    glossedTokens := [("Camacho's", ""), ("inspecting", ""), ("the", ""), ("package", ""), ("triggered", ""), ("the", ""), ("detonator", "")]
    glossedWords := [⟨['C', 'a', 'm', 'a', 'c', 'h', 'o', '\'', 's'], [], [⟨['C', 'a', 'm', 'a', 'c', 'h', 'o', '\'', 's'], [], none⟩]⟩, ⟨['i', 'n', 's', 'p', 'e', 'c', 't', 'i', 'n', 'g'], [], [⟨['i', 'n', 's', 'p', 'e', 'c', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'a', 'c', 'k', 'a', 'g', 'e'], [], [⟨['p', 'a', 'c', 'k', 'a', 'g', 'e'], [], none⟩]⟩, ⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], [⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'e', 't', 'o', 'n', 'a', 't', 'o', 'r'], [], [⟨['d', 'e', 't', 'o', 'n', 'a', 't', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "trigger"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "gerund")] }

def ex_33a : Datum :=
  { id := "martinrosenichols2025_33a"
    source := ⟨"martin-rose-nichols-2025", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The extreme intensity of the sun's rays caused Jane's skin to burn."
    glossedTokens := [("The", ""), ("extreme", ""), ("intensity", ""), ("of", ""), ("the", ""), ("sun's", ""), ("rays", ""), ("caused", ""), ("Jane's", ""), ("skin", ""), ("to", ""), ("burn", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], [⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'u', 'n', '\'', 's'], [], [⟨['s', 'u', 'n', '\'', 's'], [], none⟩]⟩, ⟨['r', 'a', 'y', 's'], [], [⟨['r', 'a', 'y', 's'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e', '\'', 's'], [], [⟨['J', 'a', 'n', 'e', '\'', 's'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "degree")] }

def ex_33b : Datum :=
  { id := "martinrosenichols2025_33b"
    source := ⟨"martin-rose-nichols-2025", "(33b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The extreme intensity of the sun's rays burned Jane's skin."
    glossedTokens := [("The", ""), ("extreme", ""), ("intensity", ""), ("of", ""), ("the", ""), ("sun's", ""), ("rays", ""), ("burned", ""), ("Jane's", ""), ("skin", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], [⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'u', 'n', '\'', 's'], [], [⟨['s', 'u', 'n', '\'', 's'], [], none⟩]⟩, ⟨['r', 'a', 'y', 's'], [], [⟨['r', 'a', 'y', 's'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e', '\'', 's'], [], [⟨['J', 'a', 'n', 'e', '\'', 's'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_34a : Datum :=
  { id := "martinrosenichols2025_34a"
    source := ⟨"martin-rose-nichols-2025", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The very poor quality of the plastic caused it to melt."
    glossedTokens := [("The", ""), ("very", ""), ("poor", ""), ("quality", ""), ("of", ""), ("the", ""), ("plastic", ""), ("caused", ""), ("it", ""), ("to", ""), ("melt", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['v', 'e', 'r', 'y'], [], [⟨['v', 'e', 'r', 'y'], [], none⟩]⟩, ⟨['p', 'o', 'o', 'r'], [], [⟨['p', 'o', 'o', 'r'], [], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], [⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't'], [], [⟨['m', 'e', 'l', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "degree")] }

def ex_34b : Datum :=
  { id := "martinrosenichols2025_34b"
    source := ⟨"martin-rose-nichols-2025", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The very poor quality of the plastic melted it."
    glossedTokens := [("The", ""), ("very", ""), ("poor", ""), ("quality", ""), ("of", ""), ("the", ""), ("plastic", ""), ("melted", ""), ("it", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['v', 'e', 'r', 'y'], [], [⟨['v', 'e', 'r', 'y'], [], none⟩]⟩, ⟨['p', 'o', 'o', 'r'], [], [⟨['p', 'o', 'o', 'r'], [], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], [⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], [⟨['p', 'l', 'a', 's', 't', 'i', 'c'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_35a : Datum :=
  { id := "martinrosenichols2025_35a"
    source := ⟨"martin-rose-nichols-2025", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The intensity of the winds caused the car to be buried under sand and debris."
    glossedTokens := [("The", ""), ("intensity", ""), ("of", ""), ("the", ""), ("winds", ""), ("caused", ""), ("the", ""), ("car", ""), ("to", ""), ("be", ""), ("buried", ""), ("under", ""), ("sand", ""), ("and", ""), ("debris", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'i', 'n', 'd', 's'], [], [⟨['w', 'i', 'n', 'd', 's'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'i', 'e', 'd'], [], [⟨['b', 'u', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['u', 'n', 'd', 'e', 'r'], [], [⟨['u', 'n', 'd', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'a', 'n', 'd'], [], [⟨['s', 'a', 'n', 'd'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'e', 'b', 'r', 'i', 's'], [], [⟨['d', 'e', 'b', 'r', 'i', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "verb", some "bury"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "degree")] }

def ex_35b : Datum :=
  { id := "martinrosenichols2025_35b"
    source := ⟨"martin-rose-nichols-2025", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The intensity of the winds buried the car under sand and debris."
    glossedTokens := [("The", ""), ("intensity", ""), ("of", ""), ("the", ""), ("winds", ""), ("buried", ""), ("the", ""), ("car", ""), ("under", ""), ("sand", ""), ("and", ""), ("debris", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'i', 'n', 'd', 's'], [], [⟨['w', 'i', 'n', 'd', 's'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'i', 'e', 'd'], [], [⟨['b', 'u', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩, ⟨['u', 'n', 'd', 'e', 'r'], [], [⟨['u', 'n', 'd', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'a', 'n', 'd'], [], [⟨['s', 'a', 'n', 'd'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'e', 'b', 'r', 'i', 's'], [], [⟨['d', 'e', 'b', 'r', 'i', 's'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "bury"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_36a : Datum :=
  { id := "martinrosenichols2025_36a"
    source := ⟨"martin-rose-nichols-2025", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The intensity of the storm caused the town's sewer system to flood."
    glossedTokens := [("The", ""), ("intensity", ""), ("of", ""), ("the", ""), ("storm", ""), ("caused", ""), ("the", ""), ("town's", ""), ("sewer", ""), ("system", ""), ("to", ""), ("flood", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 't', 'o', 'r', 'm'], [], [⟨['s', 't', 'o', 'r', 'm'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'o', 'w', 'n', '\'', 's'], [], [⟨['t', 'o', 'w', 'n', '\'', 's'], [], none⟩]⟩, ⟨['s', 'e', 'w', 'e', 'r'], [], [⟨['s', 'e', 'w', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'y', 's', 't', 'e', 'm'], [], [⟨['s', 'y', 's', 't', 'e', 'm'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "degree")] }

def ex_36b : Datum :=
  { id := "martinrosenichols2025_36b"
    source := ⟨"martin-rose-nichols-2025", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The intensity of the storm flooded the town's sewer system."
    glossedTokens := [("The", ""), ("intensity", ""), ("of", ""), ("the", ""), ("storm", ""), ("flooded", ""), ("the", ""), ("town's", ""), ("sewer", ""), ("system", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 't', 'o', 'r', 'm'], [], [⟨['s', 't', 'o', 'r', 'm'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['t', 'o', 'w', 'n', '\'', 's'], [], [⟨['t', 'o', 'w', 'n', '\'', 's'], [], none⟩]⟩, ⟨['s', 'e', 'w', 'e', 'r'], [], [⟨['s', 'e', 'w', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'y', 's', 't', 'e', 'm'], [], [⟨['s', 'y', 's', 't', 'e', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_37a : Datum :=
  { id := "martinrosenichols2025_37a"
    source := ⟨"martin-rose-nichols-2025", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Such a terrible level of betrayal burned his soul."
    glossedTokens := [("Such", ""), ("a", ""), ("terrible", ""), ("level", ""), ("of", ""), ("betrayal", ""), ("burned", ""), ("his", ""), ("soul", "")]
    glossedWords := [⟨['S', 'u', 'c', 'h'], [], [⟨['S', 'u', 'c', 'h'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['t', 'e', 'r', 'r', 'i', 'b', 'l', 'e'], [], [⟨['t', 'e', 'r', 'r', 'i', 'b', 'l', 'e'], [], none⟩]⟩, ⟨['l', 'e', 'v', 'e', 'l'], [], [⟨['l', 'e', 'v', 'e', 'l'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['b', 'e', 't', 'r', 'a', 'y', 'a', 'l'], [], [⟨['b', 'e', 't', 'r', 'a', 'y', 'a', 'l'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['s', 'o', 'u', 'l'], [], [⟨['s', 'o', 'u', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "degree")] }

def ex_37b : Datum :=
  { id := "martinrosenichols2025_37b"
    source := ⟨"martin-rose-nichols-2025", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The extraordinary quality of Gould's performance melted my heart."
    glossedTokens := [("The", ""), ("extraordinary", ""), ("quality", ""), ("of", ""), ("Gould's", ""), ("performance", ""), ("melted", ""), ("my", ""), ("heart", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'x', 't', 'r', 'a', 'o', 'r', 'd', 'i', 'n', 'a', 'r', 'y'], [], [⟨['e', 'x', 't', 'r', 'a', 'o', 'r', 'd', 'i', 'n', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], [⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['G', 'o', 'u', 'l', 'd', '\'', 's'], [], [⟨['G', 'o', 'u', 'l', 'd', '\'', 's'], [], none⟩]⟩, ⟨['p', 'e', 'r', 'f', 'o', 'r', 'm', 'a', 'n', 'c', 'e'], [], [⟨['p', 'e', 'r', 'f', 'o', 'r', 'm', 'a', 'n', 'c', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['h', 'e', 'a', 'r', 't'], [], [⟨['h', 'e', 'a', 'r', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "degree")] }

def ex_37c : Datum :=
  { id := "martinrosenichols2025_37c"
    source := ⟨"martin-rose-nichols-2025", "(37c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The extreme intensity of the moment flooded me with thoughts."
    glossedTokens := [("The", ""), ("extreme", ""), ("intensity", ""), ("of", ""), ("the", ""), ("moment", ""), ("flooded", ""), ("me", ""), ("with", ""), ("thoughts", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], [⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'o', 'm', 'e', 'n', 't'], [], [⟨['m', 'o', 'm', 'e', 'n', 't'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'e'], [], [⟨['m', 'e'], [], none⟩]⟩, ⟨['w', 'i', 't', 'h'], [], [⟨['w', 'i', 't', 'h'], [], none⟩]⟩, ⟨['t', 'h', 'o', 'u', 'g', 'h', 't', 's'], [], [⟨['t', 'h', 'o', 'u', 'g', 'h', 't', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "degree")] }

def ex_37d : Datum :=
  { id := "martinrosenichols2025_37d"
    source := ⟨"martin-rose-nichols-2025", "(37d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The extreme degree of this traumatic experience buried the painful memories deep in her subconscious."
    glossedTokens := [("The", ""), ("extreme", ""), ("degree", ""), ("of", ""), ("this", ""), ("traumatic", ""), ("experience", ""), ("buried", ""), ("the", ""), ("painful", ""), ("memories", ""), ("deep", ""), ("in", ""), ("her", ""), ("subconscious", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], [⟨['e', 'x', 't', 'r', 'e', 'm', 'e'], [], none⟩]⟩, ⟨['d', 'e', 'g', 'r', 'e', 'e'], [], [⟨['d', 'e', 'g', 'r', 'e', 'e'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'i', 's'], [], [⟨['t', 'h', 'i', 's'], [], none⟩]⟩, ⟨['t', 'r', 'a', 'u', 'm', 'a', 't', 'i', 'c'], [], [⟨['t', 'r', 'a', 'u', 'm', 'a', 't', 'i', 'c'], [], none⟩]⟩, ⟨['e', 'x', 'p', 'e', 'r', 'i', 'e', 'n', 'c', 'e'], [], [⟨['e', 'x', 'p', 'e', 'r', 'i', 'e', 'n', 'c', 'e'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'i', 'e', 'd'], [], [⟨['b', 'u', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'a', 'i', 'n', 'f', 'u', 'l'], [], [⟨['p', 'a', 'i', 'n', 'f', 'u', 'l'], [], none⟩]⟩, ⟨['m', 'e', 'm', 'o', 'r', 'i', 'e', 's'], [], [⟨['m', 'e', 'm', 'o', 'r', 'i', 'e', 's'], [], none⟩]⟩, ⟨['d', 'e', 'e', 'p'], [], [⟨['d', 'e', 'e', 'p'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'u', 'b', 'c', 'o', 'n', 's', 'c', 'i', 'o', 'u', 's'], [], [⟨['s', 'u', 'b', 'c', 'o', 'n', 's', 'c', 'i', 'o', 'u', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "bury"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "abstract"), ("subject", "degree")] }

def ex_38b : Datum :=
  { id := "martinrosenichols2025_38b"
    source := ⟨"martin-rose-nichols-2025", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The appalling quality of the bread damaged the digestive tract and resulted in chronic malnutrition."
    glossedTokens := [("The", ""), ("appalling", ""), ("quality", ""), ("of", ""), ("the", ""), ("bread", ""), ("damaged", ""), ("the", ""), ("digestive", ""), ("tract", ""), ("and", ""), ("resulted", ""), ("in", ""), ("chronic", ""), ("malnutrition", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'p', 'p', 'a', 'l', 'l', 'i', 'n', 'g'], [], [⟨['a', 'p', 'p', 'a', 'l', 'l', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], [⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'e', 'a', 'd'], [], [⟨['b', 'r', 'e', 'a', 'd'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'i', 'g', 'e', 's', 't', 'i', 'v', 'e'], [], [⟨['d', 'i', 'g', 'e', 's', 't', 'i', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'r', 'a', 'c', 't'], [], [⟨['t', 'r', 'a', 'c', 't'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['r', 'e', 's', 'u', 'l', 't', 'e', 'd'], [], [⟨['r', 'e', 's', 'u', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['c', 'h', 'r', 'o', 'n', 'i', 'c'], [], [⟨['c', 'h', 'r', 'o', 'n', 'i', 'c'], [], none⟩]⟩, ⟨['m', 'a', 'l', 'n', 'u', 't', 'r', 'i', 't', 'i', 'o', 'n'], [], [⟨['m', 'a', 'l', 'n', 'u', 't', 'r', 'i', 't', 'i', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_39a : Datum :=
  { id := "martinrosenichols2025_39a"
    source := ⟨"martin-rose-nichols-2025", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The high levels of the virus cause an overwhelming inflammatory response to be triggered."
    glossedTokens := [("The", ""), ("high", ""), ("levels", ""), ("of", ""), ("the", ""), ("virus", ""), ("cause", ""), ("an", ""), ("overwhelming", ""), ("inflammatory", ""), ("response", ""), ("to", ""), ("be", ""), ("triggered", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['h', 'i', 'g', 'h'], [], [⟨['h', 'i', 'g', 'h'], [], none⟩]⟩, ⟨['l', 'e', 'v', 'e', 'l', 's'], [], [⟨['l', 'e', 'v', 'e', 'l', 's'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['v', 'i', 'r', 'u', 's'], [], [⟨['v', 'i', 'r', 'u', 's'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e'], [], [⟨['c', 'a', 'u', 's', 'e'], [], none⟩]⟩, ⟨['a', 'n'], [], [⟨['a', 'n'], [], none⟩]⟩, ⟨['o', 'v', 'e', 'r', 'w', 'h', 'e', 'l', 'm', 'i', 'n', 'g'], [], [⟨['o', 'v', 'e', 'r', 'w', 'h', 'e', 'l', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['i', 'n', 'f', 'l', 'a', 'm', 'm', 'a', 't', 'o', 'r', 'y'], [], [⟨['i', 'n', 'f', 'l', 'a', 'm', 'm', 'a', 't', 'o', 'r', 'y'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'o', 'n', 's', 'e'], [], [⟨['r', 'e', 's', 'p', 'o', 'n', 's', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], [⟨['t', 'r', 'i', 'g', 'g', 'e', 'r', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨13, 1, "verb", some "trigger"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "degree")] }

def ex_39b : Datum :=
  { id := "martinrosenichols2025_39b"
    source := ⟨"martin-rose-nichols-2025", "(39b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The high levels of the virus trigger an overwhelming inflammatory response."
    glossedTokens := [("The", ""), ("high", ""), ("levels", ""), ("of", ""), ("the", ""), ("virus", ""), ("trigger", ""), ("an", ""), ("overwhelming", ""), ("inflammatory", ""), ("response", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['h', 'i', 'g', 'h'], [], [⟨['h', 'i', 'g', 'h'], [], none⟩]⟩, ⟨['l', 'e', 'v', 'e', 'l', 's'], [], [⟨['l', 'e', 'v', 'e', 'l', 's'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['v', 'i', 'r', 'u', 's'], [], [⟨['v', 'i', 'r', 'u', 's'], [], none⟩]⟩, ⟨['t', 'r', 'i', 'g', 'g', 'e', 'r'], [], [⟨['t', 'r', 'i', 'g', 'g', 'e', 'r'], [], none⟩]⟩, ⟨['a', 'n'], [], [⟨['a', 'n'], [], none⟩]⟩, ⟨['o', 'v', 'e', 'r', 'w', 'h', 'e', 'l', 'm', 'i', 'n', 'g'], [], [⟨['o', 'v', 'e', 'r', 'w', 'h', 'e', 'l', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['i', 'n', 'f', 'l', 'a', 'm', 'm', 'a', 't', 'o', 'r', 'y'], [], [⟨['i', 'n', 'f', 'l', 'a', 'm', 'm', 'a', 't', 'o', 'r', 'y'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'o', 'n', 's', 'e'], [], [⟨['r', 'e', 's', 'p', 'o', 'n', 's', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "trigger"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_40a : Datum :=
  { id := "martinrosenichols2025_40a"
    source := ⟨"martin-rose-nichols-2025", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The poor quality of the potting soil caused my plants to die."
    glossedTokens := [("The", ""), ("poor", ""), ("quality", ""), ("of", ""), ("the", ""), ("potting", ""), ("soil", ""), ("caused", ""), ("my", ""), ("plants", ""), ("to", ""), ("die", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'o', 'o', 'r'], [], [⟨['p', 'o', 'o', 'r'], [], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], [⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'o', 't', 't', 'i', 'n', 'g'], [], [⟨['p', 'o', 't', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['s', 'o', 'i', 'l'], [], [⟨['s', 'o', 'i', 'l'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['p', 'l', 'a', 'n', 't', 's'], [], [⟨['p', 'l', 'a', 'n', 't', 's'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['d', 'i', 'e'], [], [⟨['d', 'i', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "verb", some "die"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "degree")] }

def ex_40b : Datum :=
  { id := "martinrosenichols2025_40b"
    source := ⟨"martin-rose-nichols-2025", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The poor quality of the potting soil killed my plants."
    glossedTokens := [("The", ""), ("poor", ""), ("quality", ""), ("of", ""), ("the", ""), ("potting", ""), ("soil", ""), ("killed", ""), ("my", ""), ("plants", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'o', 'o', 'r'], [], [⟨['p', 'o', 'o', 'r'], [], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], [⟨['q', 'u', 'a', 'l', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'o', 't', 't', 'i', 'n', 'g'], [], [⟨['p', 'o', 't', 't', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['s', 'o', 'i', 'l'], [], [⟨['s', 'o', 'i', 'l'], [], none⟩]⟩, ⟨['k', 'i', 'l', 'l', 'e', 'd'], [], [⟨['k', 'i', 'l', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['p', 'l', 'a', 'n', 't', 's'], [], [⟨['p', 'l', 'a', 'n', 't', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "kill"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_41b : Datum :=
  { id := "martinrosenichols2025_41b"
    source := ⟨"martin-rose-nichols-2025", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The moisture level of the wound changed the electrical signal measured by the sensor."
    glossedTokens := [("The", ""), ("moisture", ""), ("level", ""), ("of", ""), ("the", ""), ("wound", ""), ("changed", ""), ("the", ""), ("electrical", ""), ("signal", ""), ("measured", ""), ("by", ""), ("the", ""), ("sensor", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'o', 'i', 's', 't', 'u', 'r', 'e'], [], [⟨['m', 'o', 'i', 's', 't', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['l', 'e', 'v', 'e', 'l'], [], [⟨['l', 'e', 'v', 'e', 'l'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'u', 'n', 'd'], [], [⟨['w', 'o', 'u', 'n', 'd'], [], none⟩]⟩, ⟨['c', 'h', 'a', 'n', 'g', 'e', 'd'], [], [⟨['c', 'h', 'a', 'n', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'l', 'e', 'c', 't', 'r', 'i', 'c', 'a', 'l'], [], [⟨['e', 'l', 'e', 'c', 't', 'r', 'i', 'c', 'a', 'l'], [], none⟩]⟩, ⟨['s', 'i', 'g', 'n', 'a', 'l'], [], [⟨['s', 'i', 'g', 'n', 'a', 'l'], [], none⟩]⟩, ⟨['m', 'e', 'a', 's', 'u', 'r', 'e', 'd'], [], [⟨['m', 'e', 'a', 's', 'u', 'r', 'e', 'd'], [], none⟩]⟩, ⟨['b', 'y'], [], [⟨['b', 'y'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'e', 'n', 's', 'o', 'r'], [], [⟨['s', 'e', 'n', 's', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "change"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_42a : Datum :=
  { id := "martinrosenichols2025_42a"
    source := ⟨"martin-rose-nichols-2025", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A change in molecular structure broke the window."
    glossedTokens := [("A", ""), ("change", ""), ("in", ""), ("molecular", ""), ("structure", ""), ("broke", ""), ("the", ""), ("window", "")]
    glossedWords := [⟨['A'], [], [⟨['A'], [], none⟩]⟩, ⟨['c', 'h', 'a', 'n', 'g', 'e'], [], [⟨['c', 'h', 'a', 'n', 'g', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['m', 'o', 'l', 'e', 'c', 'u', 'l', 'a', 'r'], [], [⟨['m', 'o', 'l', 'e', 'c', 'u', 'l', 'a', 'r'], [], none⟩]⟩, ⟨['s', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e'], [], [⟨['s', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['b', 'r', 'o', 'k', 'e'], [], [⟨['b', 'r', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'i', 'n', 'd', 'o', 'w'], [], [⟨['w', 'i', 'n', 'd', 'o', 'w'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "break"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_42b : Datum :=
  { id := "martinrosenichols2025_42b"
    source := ⟨"martin-rose-nichols-2025", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A change in molecular structure caused the window to break."
    glossedTokens := [("A", ""), ("change", ""), ("in", ""), ("molecular", ""), ("structure", ""), ("caused", ""), ("the", ""), ("window", ""), ("to", ""), ("break", "")]
    glossedWords := [⟨['A'], [], [⟨['A'], [], none⟩]⟩, ⟨['c', 'h', 'a', 'n', 'g', 'e'], [], [⟨['c', 'h', 'a', 'n', 'g', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['m', 'o', 'l', 'e', 'c', 'u', 'l', 'a', 'r'], [], [⟨['m', 'o', 'l', 'e', 'c', 'u', 'l', 'a', 'r'], [], none⟩]⟩, ⟨['s', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e'], [], [⟨['s', 't', 'r', 'u', 'c', 't', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'i', 'n', 'd', 'o', 'w'], [], [⟨['w', 'i', 'n', 'd', 'o', 'w'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'r', 'e', 'a', 'k'], [], [⟨['b', 'r', 'e', 'a', 'k'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "verb", some "break"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "event")] }

def ex_42c : Datum :=
  { id := "martinrosenichols2025_42c"
    source := ⟨"martin-rose-nichols-2025", "(42c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The low air pressure boiled the water."
    glossedTokens := [("The", ""), ("low", ""), ("air", ""), ("pressure", ""), ("boiled", ""), ("the", ""), ("water", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'w'], [], [⟨['l', 'o', 'w'], [], none⟩]⟩, ⟨['a', 'i', 'r'], [], [⟨['a', 'i', 'r'], [], none⟩]⟩, ⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], [⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['b', 'o', 'i', 'l', 'e', 'd'], [], [⟨['b', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], [], [⟨['w', 'a', 't', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "boil"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_42d : Datum :=
  { id := "martinrosenichols2025_42d"
    source := ⟨"martin-rose-nichols-2025", "(42d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The low air pressure caused the water to boil."
    glossedTokens := [("The", ""), ("low", ""), ("air", ""), ("pressure", ""), ("caused", ""), ("the", ""), ("water", ""), ("to", ""), ("boil", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'w'], [], [⟨['l', 'o', 'w'], [], none⟩]⟩, ⟨['a', 'i', 'r'], [], [⟨['a', 'i', 'r'], [], none⟩]⟩, ⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], [⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], [], [⟨['w', 'a', 't', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'o', 'i', 'l'], [], [⟨['b', 'o', 'i', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "verb", some "boil"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "event")] }

def ex_43a : Datum :=
  { id := "martinrosenichols2025_43a"
    source := ⟨"martin-rose-nichols-2025", "(43a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The movement broke the weak clots in the claw marks on his shoulder."
    glossedTokens := [("The", ""), ("movement", ""), ("broke", ""), ("the", ""), ("weak", ""), ("clots", ""), ("in", ""), ("the", ""), ("claw", ""), ("marks", ""), ("on", ""), ("his", ""), ("shoulder", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'o', 'v', 'e', 'm', 'e', 'n', 't'], [], [⟨['m', 'o', 'v', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩, ⟨['b', 'r', 'o', 'k', 'e'], [], [⟨['b', 'r', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'e', 'a', 'k'], [], [⟨['w', 'e', 'a', 'k'], [], none⟩]⟩, ⟨['c', 'l', 'o', 't', 's'], [], [⟨['c', 'l', 'o', 't', 's'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'l', 'a', 'w'], [], [⟨['c', 'l', 'a', 'w'], [], none⟩]⟩, ⟨['m', 'a', 'r', 'k', 's'], [], [⟨['m', 'a', 'r', 'k', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['s', 'h', 'o', 'u', 'l', 'd', 'e', 'r'], [], [⟨['s', 'h', 'o', 'u', 'l', 'd', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "break"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_43b : Datum :=
  { id := "martinrosenichols2025_43b"
    source := ⟨"martin-rose-nichols-2025", "(43b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Intense conflagrations burn all of the dried peat in a forest."
    glossedTokens := [("Intense", ""), ("conflagrations", ""), ("burn", ""), ("all", ""), ("of", ""), ("the", ""), ("dried", ""), ("peat", ""), ("in", ""), ("a", ""), ("forest", "")]
    glossedWords := [⟨['I', 'n', 't', 'e', 'n', 's', 'e'], [], [⟨['I', 'n', 't', 'e', 'n', 's', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'n', 'f', 'l', 'a', 'g', 'r', 'a', 't', 'i', 'o', 'n', 's'], [], [⟨['c', 'o', 'n', 'f', 'l', 'a', 'g', 'r', 'a', 't', 'i', 'o', 'n', 's'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩, ⟨['a', 'l', 'l'], [], [⟨['a', 'l', 'l'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'e', 'd'], [], [⟨['d', 'r', 'i', 'e', 'd'], [], none⟩]⟩, ⟨['p', 'e', 'a', 't'], [], [⟨['p', 'e', 'a', 't'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['f', 'o', 'r', 'e', 's', 't'], [], [⟨['f', 'o', 'r', 'e', 's', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_43c : Datum :=
  { id := "martinrosenichols2025_43c"
    source := ⟨"martin-rose-nichols-2025", "(43c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The heatwave boiled our pipes so it was only hot water."
    glossedTokens := [("The", ""), ("heatwave", ""), ("boiled", ""), ("our", ""), ("pipes", ""), ("so", ""), ("it", ""), ("was", ""), ("only", ""), ("hot", ""), ("water", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'w', 'a', 'v', 'e'], [], [⟨['h', 'e', 'a', 't', 'w', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['b', 'o', 'i', 'l', 'e', 'd'], [], [⟨['b', 'o', 'i', 'l', 'e', 'd'], [], none⟩]⟩, ⟨['o', 'u', 'r'], [], [⟨['o', 'u', 'r'], [], none⟩]⟩, ⟨['p', 'i', 'p', 'e', 's'], [], [⟨['p', 'i', 'p', 'e', 's'], [], none⟩]⟩, ⟨['s', 'o'], [], [⟨['s', 'o'], [], none⟩]⟩, ⟨['i', 't'], [], [⟨['i', 't'], [], none⟩]⟩, ⟨['w', 'a', 's'], [], [⟨['w', 'a', 's'], [], none⟩]⟩, ⟨['o', 'n', 'l', 'y'], [], [⟨['o', 'n', 'l', 'y'], [], none⟩]⟩, ⟨['h', 'o', 't'], [], [⟨['h', 'o', 't'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], [], [⟨['w', 'a', 't', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "boil"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_45a : Datum :=
  { id := "martinrosenichols2025_45a"
    source := ⟨"martin-rose-nichols-2025", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The accident caused her skin to burn."
    glossedTokens := [("The", ""), ("accident", ""), ("caused", ""), ("her", ""), ("skin", ""), ("to", ""), ("burn", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't'], [], [⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "event")] }

def ex_45b : Datum :=
  { id := "martinrosenichols2025_45b"
    source := ⟨"martin-rose-nichols-2025", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The accident burned her skin."
    glossedTokens := [("The", ""), ("accident", ""), ("burned", ""), ("her", ""), ("skin", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't'], [], [⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_46a : Datum :=
  { id := "martinrosenichols2025_46a"
    source := ⟨"martin-rose-nichols-2025", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The demolition of the wall caused the basement to flood."
    glossedTokens := [("The", ""), ("demolition", ""), ("of", ""), ("the", ""), ("wall", ""), ("caused", ""), ("the", ""), ("basement", ""), ("to", ""), ("flood", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'e', 'm', 'o', 'l', 'i', 't', 'i', 'o', 'n'], [], [⟨['d', 'e', 'm', 'o', 'l', 'i', 't', 'i', 'o', 'n'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'a', 'l', 'l'], [], [⟨['w', 'a', 'l', 'l'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], [⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "event")] }

def ex_46b : Datum :=
  { id := "martinrosenichols2025_46b"
    source := ⟨"martin-rose-nichols-2025", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The demolition of the wall flooded the basement."
    glossedTokens := [("The", ""), ("demolition", ""), ("of", ""), ("the", ""), ("wall", ""), ("flooded", ""), ("the", ""), ("basement", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'e', 'm', 'o', 'l', 'i', 't', 'i', 'o', 'n'], [], [⟨['d', 'e', 'm', 'o', 'l', 'i', 't', 'i', 'o', 'n'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'a', 'l', 'l'], [], [⟨['w', 'a', 'l', 'l'], [], none⟩]⟩, ⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], [⟨['f', 'l', 'o', 'o', 'd', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], [⟨['b', 'a', 's', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "flood"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_47a : Datum :=
  { id := "martinrosenichols2025_47a"
    source := ⟨"martin-rose-nichols-2025", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The accident destroyed her skin."
    glossedTokens := [("The", ""), ("accident", ""), ("destroyed", ""), ("her", ""), ("skin", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't'], [], [⟨['a', 'c', 'c', 'i', 'd', 'e', 'n', 't'], [], none⟩]⟩, ⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], [⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], none⟩]⟩, ⟨['h', 'e', 'r'], [], [⟨['h', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'k', 'i', 'n'], [], [⟨['s', 'k', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "verb", some "destroy"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_47b : Datum :=
  { id := "martinrosenichols2025_47b"
    source := ⟨"martin-rose-nichols-2025", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The low air pressure changed the water."
    glossedTokens := [("The", ""), ("low", ""), ("air", ""), ("pressure", ""), ("changed", ""), ("the", ""), ("water", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'w'], [], [⟨['l', 'o', 'w'], [], none⟩]⟩, ⟨['a', 'i', 'r'], [], [⟨['a', 'i', 'r'], [], none⟩]⟩, ⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], [⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['c', 'h', 'a', 'n', 'g', 'e', 'd'], [], [⟨['c', 'h', 'a', 'n', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], [], [⟨['w', 'a', 't', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "change"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "event")] }

def ex_62a : Datum :=
  { id := "martinrosenichols2025_62a"
    source := ⟨"martin-rose-nichols-2025", "(62a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Lack of humidity burned them."
    glossedTokens := [("Lack", ""), ("of", ""), ("humidity", ""), ("burned", ""), ("them", "")]
    glossedWords := [⟨['L', 'a', 'c', 'k'], [], [⟨['L', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['h', 'u', 'm', 'i', 'd', 'i', 't', 'y'], [], [⟨['h', 'u', 'm', 'i', 'd', 'i', 't', 'y'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n', 'e', 'd'], [], [⟨['b', 'u', 'r', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'm'], [], [⟨['t', 'h', 'e', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_62b : Datum :=
  { id := "martinrosenichols2025_62b"
    source := ⟨"martin-rose-nichols-2025", "(62b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Lack of water will burn out the pump."
    glossedTokens := [("Lack", ""), ("of", ""), ("water", ""), ("will", ""), ("burn", ""), ("out", ""), ("the", ""), ("pump", "")]
    glossedWords := [⟨['L', 'a', 'c', 'k'], [], [⟨['L', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['w', 'a', 't', 'e', 'r'], [], [⟨['w', 'a', 't', 'e', 'r'], [], none⟩]⟩, ⟨['w', 'i', 'l', 'l'], [], [⟨['w', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['b', 'u', 'r', 'n'], [], [⟨['b', 'u', 'r', 'n'], [], none⟩]⟩, ⟨['o', 'u', 't'], [], [⟨['o', 'u', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'u', 'm', 'p'], [], [⟨['p', 'u', 'm', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "burn"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_62d : Datum :=
  { id := "martinrosenichols2025_62d"
    source := ⟨"martin-rose-nichols-2025", "(62d)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The lack of suspension lifts the other wheels up."
    glossedTokens := [("The", ""), ("lack", ""), ("of", ""), ("suspension", ""), ("lifts", ""), ("the", ""), ("other", ""), ("wheels", ""), ("up", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['s', 'u', 's', 'p', 'e', 'n', 's', 'i', 'o', 'n'], [], [⟨['s', 'u', 's', 'p', 'e', 'n', 's', 'i', 'o', 'n'], [], none⟩]⟩, ⟨['l', 'i', 'f', 't', 's'], [], [⟨['l', 'i', 'f', 't', 's'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['o', 't', 'h', 'e', 'r'], [], [⟨['o', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'e', 'l', 's'], [], [⟨['w', 'h', 'e', 'e', 'l', 's'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "verb", some "lift"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_62e : Datum :=
  { id := "martinrosenichols2025_62e"
    source := ⟨"martin-rose-nichols-2025", "(62e)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Lack of holes locks the electrons into positions from which they cannot move."
    glossedTokens := [("Lack", ""), ("of", ""), ("holes", ""), ("locks", ""), ("the", ""), ("electrons", ""), ("into", ""), ("positions", ""), ("from", ""), ("which", ""), ("they", ""), ("cannot", ""), ("move", "")]
    glossedWords := [⟨['L', 'a', 'c', 'k'], [], [⟨['L', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['h', 'o', 'l', 'e', 's'], [], [⟨['h', 'o', 'l', 'e', 's'], [], none⟩]⟩, ⟨['l', 'o', 'c', 'k', 's'], [], [⟨['l', 'o', 'c', 'k', 's'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['e', 'l', 'e', 'c', 't', 'r', 'o', 'n', 's'], [], [⟨['e', 'l', 'e', 'c', 't', 'r', 'o', 'n', 's'], [], none⟩]⟩, ⟨['i', 'n', 't', 'o'], [], [⟨['i', 'n', 't', 'o'], [], none⟩]⟩, ⟨['p', 'o', 's', 'i', 't', 'i', 'o', 'n', 's'], [], [⟨['p', 'o', 's', 'i', 't', 'i', 'o', 'n', 's'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['w', 'h', 'i', 'c', 'h'], [], [⟨['w', 'h', 'i', 'c', 'h'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'y'], [], [⟨['t', 'h', 'e', 'y'], [], none⟩]⟩, ⟨['c', 'a', 'n', 'n', 'o', 't'], [], [⟨['c', 'a', 'n', 'n', 'o', 't'], [], none⟩]⟩, ⟨['m', 'o', 'v', 'e'], [], [⟨['m', 'o', 'v', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "lock"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_65a : Datum :=
  { id := "martinrosenichols2025_65a"
    source := ⟨"martin-rose-nichols-2025", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that my lips lack hydration cracks them."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("my", ""), ("lips", ""), ("lack", ""), ("hydration", ""), ("cracks", ""), ("them", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['l', 'i', 'p', 's'], [], [⟨['l', 'i', 'p', 's'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['h', 'y', 'd', 'r', 'a', 't', 'i', 'o', 'n'], [], [⟨['h', 'y', 'd', 'r', 'a', 't', 'i', 'o', 'n'], [], none⟩]⟩, ⟨['c', 'r', 'a', 'c', 'k', 's'], [], [⟨['c', 'r', 'a', 'c', 'k', 's'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'm'], [], [⟨['t', 'h', 'e', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "crack"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "fact")] }

def ex_65b : Datum :=
  { id := "martinrosenichols2025_65b"
    source := ⟨"martin-rose-nichols-2025", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fact that my lips lack hydration destroys them."
    glossedTokens := [("The", ""), ("fact", ""), ("that", ""), ("my", ""), ("lips", ""), ("lack", ""), ("hydration", ""), ("destroys", ""), ("them", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'a', 'c', 't'], [], [⟨['f', 'a', 'c', 't'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['m', 'y'], [], [⟨['m', 'y'], [], none⟩]⟩, ⟨['l', 'i', 'p', 's'], [], [⟨['l', 'i', 'p', 's'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['h', 'y', 'd', 'r', 'a', 't', 'i', 'o', 'n'], [], [⟨['h', 'y', 'd', 'r', 'a', 't', 'i', 'o', 'n'], [], none⟩]⟩, ⟨['d', 'e', 's', 't', 'r', 'o', 'y', 's'], [], [⟨['d', 'e', 's', 't', 'r', 'o', 'y', 's'], [], none⟩]⟩, ⟨['t', 'h', 'e', 'm'], [], [⟨['t', 'h', 'e', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "destroy"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "fact")] }

def ex_66a : Datum :=
  { id := "martinrosenichols2025_66a"
    source := ⟨"martin-rose-nichols-2025", "(66a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The intensity of the heat melted the door handles and allowed the rescuers to open the car."
    glossedTokens := [("The", ""), ("intensity", ""), ("of", ""), ("the", ""), ("heat", ""), ("melted", ""), ("the", ""), ("door", ""), ("handles", ""), ("and", ""), ("allowed", ""), ("the", ""), ("rescuers", ""), ("to", ""), ("open", ""), ("the", ""), ("car", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't'], [], [⟨['h', 'e', 'a', 't'], [], none⟩]⟩, ⟨['m', 'e', 'l', 't', 'e', 'd'], [], [⟨['m', 'e', 'l', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'o', 'o', 'r'], [], [⟨['d', 'o', 'o', 'r'], [], none⟩]⟩, ⟨['h', 'a', 'n', 'd', 'l', 'e', 's'], [], [⟨['h', 'a', 'n', 'd', 'l', 'e', 's'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['a', 'l', 'l', 'o', 'w', 'e', 'd'], [], [⟨['a', 'l', 'l', 'o', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'e', 's', 'c', 'u', 'e', 'r', 's'], [], [⟨['r', 'e', 's', 'c', 'u', 'e', 'r', 's'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['o', 'p', 'e', 'n'], [], [⟨['o', 'p', 'e', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "melt"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_66b : Datum :=
  { id := "martinrosenichols2025_66b"
    source := ⟨"martin-rose-nichols-2025", "(66b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The intensity of the fire lifted the radioactive contaminants higher into the atmosphere."
    glossedTokens := [("The", ""), ("intensity", ""), ("of", ""), ("the", ""), ("fire", ""), ("lifted", ""), ("the", ""), ("radioactive", ""), ("contaminants", ""), ("higher", ""), ("into", ""), ("the", ""), ("atmosphere", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], [⟨['i', 'n', 't', 'e', 'n', 's', 'i', 't', 'y'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'i', 'r', 'e'], [], [⟨['f', 'i', 'r', 'e'], [], none⟩]⟩, ⟨['l', 'i', 'f', 't', 'e', 'd'], [], [⟨['l', 'i', 'f', 't', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['r', 'a', 'd', 'i', 'o', 'a', 'c', 't', 'i', 'v', 'e'], [], [⟨['r', 'a', 'd', 'i', 'o', 'a', 'c', 't', 'i', 'v', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'n', 't', 'a', 'm', 'i', 'n', 'a', 'n', 't', 's'], [], [⟨['c', 'o', 'n', 't', 'a', 'm', 'i', 'n', 'a', 'n', 't', 's'], [], none⟩]⟩, ⟨['h', 'i', 'g', 'h', 'e', 'r'], [], [⟨['h', 'i', 'g', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['i', 'n', 't', 'o'], [], [⟨['i', 'n', 't', 'o'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['a', 't', 'm', 'o', 's', 'p', 'h', 'e', 'r', 'e'], [], [⟨['a', 't', 'm', 'o', 's', 'p', 'h', 'e', 'r', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "verb", some "lift"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "degree")] }

def ex_78a : Datum :=
  { id := "martinrosenichols2025_78a"
    source := ⟨"martin-rose-nichols-2025", "(78a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The flat tire caused the axel to crack."
    glossedTokens := [("The", ""), ("flat", ""), ("tire", ""), ("caused", ""), ("the", ""), ("axel", ""), ("to", ""), ("crack", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'l', 'a', 't'], [], [⟨['f', 'l', 'a', 't'], [], none⟩]⟩, ⟨['t', 'i', 'r', 'e'], [], [⟨['t', 'i', 'r', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'x', 'e', 'l'], [], [⟨['a', 'x', 'e', 'l'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['c', 'r', 'a', 'c', 'k'], [], [⟨['c', 'r', 'a', 'c', 'k'], [], none⟩]⟩]
    context := "John's car tire is flat and so when driving, weight is no longer evenly distributed across the axel. As a result, the axel cracked."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "crack"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "individual")] }

def ex_78b : Datum :=
  { id := "martinrosenichols2025_78b"
    source := ⟨"martin-rose-nichols-2025", "(78b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The flat tire cracked the axel."
    glossedTokens := [("The", ""), ("flat", ""), ("tire", ""), ("cracked", ""), ("the", ""), ("axel", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'l', 'a', 't'], [], [⟨['f', 'l', 'a', 't'], [], none⟩]⟩, ⟨['t', 'i', 'r', 'e'], [], [⟨['t', 'i', 'r', 'e'], [], none⟩]⟩, ⟨['c', 'r', 'a', 'c', 'k', 'e', 'd'], [], [⟨['c', 'r', 'a', 'c', 'k', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'x', 'e', 'l'], [], [⟨['a', 'x', 'e', 'l'], [], none⟩]⟩]
    context := "John's car tire is flat and so when driving, weight is no longer evenly distributed across the axel. As a result, the axel cracked."
    judgment := .marginal
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "crack"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "individual")] }

def ex_79a : Datum :=
  { id := "martinrosenichols2025_79a"
    source := ⟨"martin-rose-nichols-2025", "(79a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The flat tire caused the axel to be damaged."
    glossedTokens := [("The", ""), ("flat", ""), ("tire", ""), ("caused", ""), ("the", ""), ("axel", ""), ("to", ""), ("be", ""), ("damaged", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'l', 'a', 't'], [], [⟨['f', 'l', 'a', 't'], [], none⟩]⟩, ⟨['t', 'i', 'r', 'e'], [], [⟨['t', 'i', 'r', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'x', 'e', 'l'], [], [⟨['a', 'x', 'e', 'l'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩]
    context := "John's car tire is flat and so when driving, weight is no longer evenly distributed across the axel. As a result, the axel is damaged."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "individual")] }

def ex_79b : Datum :=
  { id := "martinrosenichols2025_79b"
    source := ⟨"martin-rose-nichols-2025", "(79b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The flat tire damaged the axel."
    glossedTokens := [("The", ""), ("flat", ""), ("tire", ""), ("damaged", ""), ("the", ""), ("axel", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'l', 'a', 't'], [], [⟨['f', 'l', 'a', 't'], [], none⟩]⟩, ⟨['t', 'i', 'r', 'e'], [], [⟨['t', 'i', 'r', 'e'], [], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], [⟨['d', 'a', 'm', 'a', 'g', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['a', 'x', 'e', 'l'], [], [⟨['a', 'x', 'e', 'l'], [], none⟩]⟩]
    context := "John's car tire is flat and so when driving, weight is no longer evenly distributed across the axel. As a result, the axel is damaged."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "damage"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "individual")] }

def ex_80a : Datum :=
  { id := "martinrosenichols2025_80a"
    source := ⟨"martin-rose-nichols-2025", "(80a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The uneven road caused the car to crash."
    glossedTokens := [("The", ""), ("uneven", ""), ("road", ""), ("caused", ""), ("the", ""), ("car", ""), ("to", ""), ("crash", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['u', 'n', 'e', 'v', 'e', 'n'], [], [⟨['u', 'n', 'e', 'v', 'e', 'n'], [], none⟩]⟩, ⟨['r', 'o', 'a', 'd'], [], [⟨['r', 'o', 'a', 'd'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['c', 'r', 'a', 's', 'h'], [], [⟨['c', 'r', 'a', 's', 'h'], [], none⟩]⟩]
    context := "Andy is driving through the mountains and recent storms have damaged the road, making it extremely uneven. As a result, the car crashed/is destroyed."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "crash"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "individual")] }

def ex_80b : Datum :=
  { id := "martinrosenichols2025_80b"
    source := ⟨"martin-rose-nichols-2025", "(80b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The uneven road crashed the car."
    glossedTokens := [("The", ""), ("uneven", ""), ("road", ""), ("crashed", ""), ("the", ""), ("car", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['u', 'n', 'e', 'v', 'e', 'n'], [], [⟨['u', 'n', 'e', 'v', 'e', 'n'], [], none⟩]⟩, ⟨['r', 'o', 'a', 'd'], [], [⟨['r', 'o', 'a', 'd'], [], none⟩]⟩, ⟨['c', 'r', 'a', 's', 'h', 'e', 'd'], [], [⟨['c', 'r', 'a', 's', 'h', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩]
    context := "Andy is driving through the mountains and recent storms have damaged the road, making it extremely uneven. As a result, the car crashed/is destroyed."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "crash"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "individual")] }

def ex_80c : Datum :=
  { id := "martinrosenichols2025_80c"
    source := ⟨"martin-rose-nichols-2025", "(80c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The uneven road caused the car to be destroyed."
    glossedTokens := [("The", ""), ("uneven", ""), ("road", ""), ("caused", ""), ("the", ""), ("car", ""), ("to", ""), ("be", ""), ("destroyed", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['u', 'n', 'e', 'v', 'e', 'n'], [], [⟨['u', 'n', 'e', 'v', 'e', 'n'], [], none⟩]⟩, ⟨['r', 'o', 'a', 'd'], [], [⟨['r', 'o', 'a', 'd'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], [⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], none⟩]⟩]
    context := "Andy is driving through the mountains and recent storms have damaged the road, making it extremely uneven. As a result, the car crashed/is destroyed."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "verb", some "destroy"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "individual")] }

def ex_80d : Datum :=
  { id := "martinrosenichols2025_80d"
    source := ⟨"martin-rose-nichols-2025", "(80d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The uneven road destroyed the car."
    glossedTokens := [("The", ""), ("uneven", ""), ("road", ""), ("destroyed", ""), ("the", ""), ("car", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['u', 'n', 'e', 'v', 'e', 'n'], [], [⟨['u', 'n', 'e', 'v', 'e', 'n'], [], none⟩]⟩, ⟨['r', 'o', 'a', 'd'], [], [⟨['r', 'o', 'a', 'd'], [], none⟩]⟩, ⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], [⟨['d', 'e', 's', 't', 'r', 'o', 'y', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'r'], [], [⟨['c', 'a', 'r'], [], none⟩]⟩]
    context := "Andy is driving through the mountains and recent storms have damaged the road, making it extremely uneven. As a result, the car crashed/is destroyed."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "destroy"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "individual")] }

def ex_81a : Datum :=
  { id := "martinrosenichols2025_81a"
    source := ⟨"martin-rose-nichols-2025", "(81a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The manufacturing defect caused the phone to heat up."
    glossedTokens := [("The", ""), ("manufacturing", ""), ("defect", ""), ("caused", ""), ("the", ""), ("phone", ""), ("to", ""), ("heat", ""), ("up", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], [⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['d', 'e', 'f', 'e', 'c', 't'], [], [⟨['d', 'e', 'f', 'e', 'c', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't'], [], [⟨['h', 'e', 'a', 't'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩]
    context := "Suzy bought a new phone that has a manufacturing defect: when texting it heats up. After buying the phone, she texts her friend. As a result, it heated up/it is ruined."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "verb", some "heat"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "individual")] }

def ex_81b : Datum :=
  { id := "martinrosenichols2025_81b"
    source := ⟨"martin-rose-nichols-2025", "(81b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The manufacturing defect heated up the phone."
    glossedTokens := [("The", ""), ("manufacturing", ""), ("defect", ""), ("heated", ""), ("up", ""), ("the", ""), ("phone", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], [⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['d', 'e', 'f', 'e', 'c', 't'], [], [⟨['d', 'e', 'f', 'e', 'c', 't'], [], none⟩]⟩, ⟨['h', 'e', 'a', 't', 'e', 'd'], [], [⟨['h', 'e', 'a', 't', 'e', 'd'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩]
    context := "Suzy bought a new phone that has a manufacturing defect: when texting it heats up. After buying the phone, she texts her friend. As a result, it heated up/it is ruined."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "heat"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "individual")] }

def ex_81c : Datum :=
  { id := "martinrosenichols2025_81c"
    source := ⟨"martin-rose-nichols-2025", "(81c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The manufacturing defect caused the phone to be ruined."
    glossedTokens := [("The", ""), ("manufacturing", ""), ("defect", ""), ("caused", ""), ("the", ""), ("phone", ""), ("to", ""), ("be", ""), ("ruined", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], [⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['d', 'e', 'f', 'e', 'c', 't'], [], [⟨['d', 'e', 'f', 'e', 'c', 't'], [], none⟩]⟩, ⟨['c', 'a', 'u', 's', 'e', 'd'], [], [⟨['c', 'a', 'u', 's', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['r', 'u', 'i', 'n', 'e', 'd'], [], [⟨['r', 'u', 'i', 'n', 'e', 'd'], [], none⟩]⟩]
    context := "Suzy bought a new phone that has a manufacturing defect: when texting it heats up. After buying the phone, she texts her friend. As a result, it heated up/it is ruined."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨8, 1, "verb", some "ruin"⟩]
    paperFeatures := [("frame", "periphrastic"), ("sense", "physical"), ("subject", "individual")] }

def ex_81d : Datum :=
  { id := "martinrosenichols2025_81d"
    source := ⟨"martin-rose-nichols-2025", "(81d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The manufacturing defect ruined the phone."
    glossedTokens := [("The", ""), ("manufacturing", ""), ("defect", ""), ("ruined", ""), ("the", ""), ("phone", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], [⟨['m', 'a', 'n', 'u', 'f', 'a', 'c', 't', 'u', 'r', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['d', 'e', 'f', 'e', 'c', 't'], [], [⟨['d', 'e', 'f', 'e', 'c', 't'], [], none⟩]⟩, ⟨['r', 'u', 'i', 'n', 'e', 'd'], [], [⟨['r', 'u', 'i', 'n', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['p', 'h', 'o', 'n', 'e'], [], [⟨['p', 'h', 'o', 'n', 'e'], [], none⟩]⟩]
    context := "Suzy bought a new phone that has a manufacturing defect: when texting it heats up. After buying the phone, she texts her friend. As a result, it heated up/it is ruined."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "verb", some "ruin"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "individual")] }

def ex_96a : Datum :=
  { id := "martinrosenichols2025_96a"
    source := ⟨"martin-rose-nichols-2025", "(96a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sudden lack of air pressure lowered the balloon."
    glossedTokens := [("The", ""), ("sudden", ""), ("lack", ""), ("of", ""), ("air", ""), ("pressure", ""), ("lowered", ""), ("the", ""), ("balloon", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'u', 'd', 'd', 'e', 'n'], [], [⟨['s', 'u', 'd', 'd', 'e', 'n'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a', 'i', 'r'], [], [⟨['a', 'i', 'r'], [], none⟩]⟩, ⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], [⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['l', 'o', 'w', 'e', 'r', 'e', 'd'], [], [⟨['l', 'o', 'w', 'e', 'r', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'a', 'l', 'l', 'o', 'o', 'n'], [], [⟨['b', 'a', 'l', 'l', 'o', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "lower"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def ex_96b : Datum :=
  { id := "martinrosenichols2025_96b"
    source := ⟨"martin-rose-nichols-2025", "(96b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The sudden lack of air pressure dropped the balloon."
    glossedTokens := [("The", ""), ("sudden", ""), ("lack", ""), ("of", ""), ("air", ""), ("pressure", ""), ("dropped", ""), ("the", ""), ("balloon", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'u', 'd', 'd', 'e', 'n'], [], [⟨['s', 'u', 'd', 'd', 'e', 'n'], [], none⟩]⟩, ⟨['l', 'a', 'c', 'k'], [], [⟨['l', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['o', 'f'], [], [⟨['o', 'f'], [], none⟩]⟩, ⟨['a', 'i', 'r'], [], [⟨['a', 'i', 'r'], [], none⟩]⟩, ⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], [⟨['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [], none⟩]⟩, ⟨['d', 'r', 'o', 'p', 'p', 'e', 'd'], [], [⟨['d', 'r', 'o', 'p', 'p', 'e', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['b', 'a', 'l', 'l', 'o', 'o', 'n'], [], [⟨['b', 'a', 'l', 'l', 'o', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "verb", some "drop"⟩]
    paperFeatures := [("frame", "lexical"), ("sense", "physical"), ("subject", "absence")] }

def all : List Datum := [ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_9a, ex_9b, ex_9c, ex_10a, ex_10b, ex_10c, ex_12a, ex_12b, ex_13a, ex_13b, ex_13c, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_18a_damage, ex_18a_burn, ex_18b_damage, ex_18b_burn, ex_19a_destroy, ex_19a_melt, ex_19b_destroy, ex_19b_melt, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_24a, ex_24b, ex_24c, ex_25a, ex_25b, ex_26a, ex_26b, ex_27a, ex_27b, ex_33a, ex_33b, ex_34a, ex_34b, ex_35a, ex_35b, ex_36a, ex_36b, ex_37a, ex_37b, ex_37c, ex_37d, ex_38b, ex_39a, ex_39b, ex_40a, ex_40b, ex_41b, ex_42a, ex_42b, ex_42c, ex_42d, ex_43a, ex_43b, ex_43c, ex_45a, ex_45b, ex_46a, ex_46b, ex_47a, ex_47b, ex_62a, ex_62b, ex_62d, ex_62e, ex_65a, ex_65b, ex_66a, ex_66b, ex_78a, ex_78b, ex_79a, ex_79b, ex_80a, ex_80b, ex_80c, ex_80d, ex_81a, ex_81b, ex_81c, ex_81d, ex_96a, ex_96b]

/-- The construction that expresses the causal relation. -/
inductive Frame where
  /-- lexical: the transitive lexical causative, with the cause as subject -/
  | lexical
  /-- periphrastic: the verb *cause* with an infinitival complement -/
  | periphrastic
  /-- anticausative: the intransitive verb with the cause in a *from* phrase -/
  | anticausative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `frame`. -/
def frame (e : Datum) : Option Frame :=
  e.parse? "frame" [("lexical", .lexical), ("periphrastic", .periphrastic), ("anticausative", .anticausative)]

/-- The sense in which the verb is used. -/
inductive Sense where
  /-- physical: the concrete, physical sense -/
  | physical
  /-- abstract: a figurative, psychological or otherwise abstract sense -/
  | abstract
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `sense`. -/
def sense (e : Datum) : Option Sense :=
  e.parse? "sense" [("physical", .physical), ("abstract", .abstract)]

/-- What the phrase naming the cause denotes. -/
inductive Subject where
  /-- absence: an absence or omission, *the lack of sunscreen* -/
  | absence
  /-- fact: a fact, named by a *the fact that* nominal -/
  | fact
  /-- gerund: a fact or other abstract object, named by a verbal gerund -/
  | gerund
  /-- degree: a degree, named by a dimensional noun such as *quality* or *intensity* -/
  | degree
  /-- event: an event or a force -/
  | event
  /-- individual: a concrete individual -/
  | individual
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option Subject :=
  e.parse? "subject" [("absence", .absence), ("fact", .fact), ("gerund", .gerund), ("degree", .degree),
    ("event", .event), ("individual", .individual)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- verb: the causative verb under test, or in the periphrastic frame the verb under *cause* -/
  | verb
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("verb", .verb)]

/-- The verbs under test. -/
inductive Lexeme where
  /-- burn: the English verb *burn* -/
  | burn
  /-- melt: the English verb *melt* -/
  | melt
  /-- flood: the English verb *flood* -/
  | flood
  /-- kill: the English verb *kill* -/
  | kill
  /-- die: the English verb *die* -/
  | die
  /-- damage: the English verb *damage* -/
  | damage
  /-- trigger: the English verb *trigger* -/
  | trigger
  /-- change: the English verb *change* -/
  | change
  /-- activate: the English verb *activate* -/
  | activate
  /-- bury: the English verb *bury* -/
  | bury
  /-- break: the English verb *break* -/
  | break
  /-- crack: the English verb *crack* -/
  | crack
  /-- destroy: the English verb *destroy* -/
  | destroy
  /-- boil: the English verb *boil* -/
  | boil
  /-- lift: the English verb *lift* -/
  | lift
  /-- lock: the English verb *lock* -/
  | lock
  /-- crash: the English verb *crash* -/
  | crash
  /-- heat: the English verb *heat* -/
  | heat
  /-- ruin: the English verb *ruin* -/
  | ruin
  /-- lower: the English verb *lower* -/
  | lower
  /-- drop: the English verb *drop* -/
  | drop
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("burn", .burn), ("melt", .melt), ("flood", .flood), ("kill", .kill), ("die", .die), ("damage", .damage), ("trigger", .trigger), ("change", .change), ("activate", .activate), ("bury", .bury), ("break", .break), ("crack", .crack), ("destroy", .destroy), ("boil", .boil), ("lift", .lift), ("lock", .lock), ("crash", .crash), ("heat", .heat), ("ruin", .ruin), ("lower", .lower), ("drop", .drop)])

/-- The causative statements of the paper's sections 1 to 3, 4.3.1 and 6 and of its appendix. -/
inductive Example where
  | ex_5a
  | ex_5b
  | ex_6a
  | ex_6b
  | ex_7a
  | ex_7b
  | ex_9a
  | ex_9b
  | ex_9c
  | ex_10a
  | ex_10b
  | ex_10c
  | ex_12a
  | ex_12b
  | ex_13a
  | ex_13b
  | ex_13c
  | ex_14a
  | ex_14b
  | ex_15a
  | ex_15b
  | ex_16a
  | ex_16b
  | ex_18a_damage
  | ex_18a_burn
  | ex_18b_damage
  | ex_18b_burn
  | ex_19a_destroy
  | ex_19a_melt
  | ex_19b_destroy
  | ex_19b_melt
  | ex_21a
  | ex_21b
  | ex_22a
  | ex_22b
  | ex_23a
  | ex_23b
  | ex_24a
  | ex_24b
  | ex_24c
  | ex_25a
  | ex_25b
  | ex_26a
  | ex_26b
  | ex_27a
  | ex_27b
  | ex_33a
  | ex_33b
  | ex_34a
  | ex_34b
  | ex_35a
  | ex_35b
  | ex_36a
  | ex_36b
  | ex_37a
  | ex_37b
  | ex_37c
  | ex_37d
  | ex_38b
  | ex_39a
  | ex_39b
  | ex_40a
  | ex_40b
  | ex_41b
  | ex_42a
  | ex_42b
  | ex_42c
  | ex_42d
  | ex_43a
  | ex_43b
  | ex_43c
  | ex_45a
  | ex_45b
  | ex_46a
  | ex_46b
  | ex_47a
  | ex_47b
  | ex_62a
  | ex_62b
  | ex_62d
  | ex_62e
  | ex_65a
  | ex_65b
  | ex_66a
  | ex_66b
  | ex_78a
  | ex_78b
  | ex_79a
  | ex_79b
  | ex_80a
  | ex_80b
  | ex_80c
  | ex_80d
  | ex_81a
  | ex_81b
  | ex_81c
  | ex_81d
  | ex_96a
  | ex_96b
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_5a, .ex_5b, .ex_6a, .ex_6b, .ex_7a, .ex_7b, .ex_9a, .ex_9b, .ex_9c, .ex_10a, .ex_10b,
    .ex_10c, .ex_12a, .ex_12b, .ex_13a, .ex_13b, .ex_13c, .ex_14a, .ex_14b, .ex_15a, .ex_15b,
    .ex_16a, .ex_16b, .ex_18a_damage, .ex_18a_burn, .ex_18b_damage, .ex_18b_burn, .ex_19a_destroy,
    .ex_19a_melt, .ex_19b_destroy, .ex_19b_melt, .ex_21a, .ex_21b, .ex_22a, .ex_22b, .ex_23a,
    .ex_23b, .ex_24a, .ex_24b, .ex_24c, .ex_25a, .ex_25b, .ex_26a, .ex_26b, .ex_27a, .ex_27b,
    .ex_33a, .ex_33b, .ex_34a, .ex_34b, .ex_35a, .ex_35b, .ex_36a, .ex_36b, .ex_37a, .ex_37b,
    .ex_37c, .ex_37d, .ex_38b, .ex_39a, .ex_39b, .ex_40a, .ex_40b, .ex_41b, .ex_42a, .ex_42b,
    .ex_42c, .ex_42d, .ex_43a, .ex_43b, .ex_43c, .ex_45a, .ex_45b, .ex_46a, .ex_46b, .ex_47a,
    .ex_47b, .ex_62a, .ex_62b, .ex_62d, .ex_62e, .ex_65a, .ex_65b, .ex_66a, .ex_66b, .ex_78a,
    .ex_78b, .ex_79a, .ex_79b, .ex_80a, .ex_80b, .ex_80c, .ex_80d, .ex_81a, .ex_81b, .ex_81c,
    .ex_81d, .ex_96a, .ex_96b]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_5a => _root_.MartinRoseNichols2025.Examples.ex_5a
  | .ex_5b => _root_.MartinRoseNichols2025.Examples.ex_5b
  | .ex_6a => _root_.MartinRoseNichols2025.Examples.ex_6a
  | .ex_6b => _root_.MartinRoseNichols2025.Examples.ex_6b
  | .ex_7a => _root_.MartinRoseNichols2025.Examples.ex_7a
  | .ex_7b => _root_.MartinRoseNichols2025.Examples.ex_7b
  | .ex_9a => _root_.MartinRoseNichols2025.Examples.ex_9a
  | .ex_9b => _root_.MartinRoseNichols2025.Examples.ex_9b
  | .ex_9c => _root_.MartinRoseNichols2025.Examples.ex_9c
  | .ex_10a => _root_.MartinRoseNichols2025.Examples.ex_10a
  | .ex_10b => _root_.MartinRoseNichols2025.Examples.ex_10b
  | .ex_10c => _root_.MartinRoseNichols2025.Examples.ex_10c
  | .ex_12a => _root_.MartinRoseNichols2025.Examples.ex_12a
  | .ex_12b => _root_.MartinRoseNichols2025.Examples.ex_12b
  | .ex_13a => _root_.MartinRoseNichols2025.Examples.ex_13a
  | .ex_13b => _root_.MartinRoseNichols2025.Examples.ex_13b
  | .ex_13c => _root_.MartinRoseNichols2025.Examples.ex_13c
  | .ex_14a => _root_.MartinRoseNichols2025.Examples.ex_14a
  | .ex_14b => _root_.MartinRoseNichols2025.Examples.ex_14b
  | .ex_15a => _root_.MartinRoseNichols2025.Examples.ex_15a
  | .ex_15b => _root_.MartinRoseNichols2025.Examples.ex_15b
  | .ex_16a => _root_.MartinRoseNichols2025.Examples.ex_16a
  | .ex_16b => _root_.MartinRoseNichols2025.Examples.ex_16b
  | .ex_18a_damage => _root_.MartinRoseNichols2025.Examples.ex_18a_damage
  | .ex_18a_burn => _root_.MartinRoseNichols2025.Examples.ex_18a_burn
  | .ex_18b_damage => _root_.MartinRoseNichols2025.Examples.ex_18b_damage
  | .ex_18b_burn => _root_.MartinRoseNichols2025.Examples.ex_18b_burn
  | .ex_19a_destroy => _root_.MartinRoseNichols2025.Examples.ex_19a_destroy
  | .ex_19a_melt => _root_.MartinRoseNichols2025.Examples.ex_19a_melt
  | .ex_19b_destroy => _root_.MartinRoseNichols2025.Examples.ex_19b_destroy
  | .ex_19b_melt => _root_.MartinRoseNichols2025.Examples.ex_19b_melt
  | .ex_21a => _root_.MartinRoseNichols2025.Examples.ex_21a
  | .ex_21b => _root_.MartinRoseNichols2025.Examples.ex_21b
  | .ex_22a => _root_.MartinRoseNichols2025.Examples.ex_22a
  | .ex_22b => _root_.MartinRoseNichols2025.Examples.ex_22b
  | .ex_23a => _root_.MartinRoseNichols2025.Examples.ex_23a
  | .ex_23b => _root_.MartinRoseNichols2025.Examples.ex_23b
  | .ex_24a => _root_.MartinRoseNichols2025.Examples.ex_24a
  | .ex_24b => _root_.MartinRoseNichols2025.Examples.ex_24b
  | .ex_24c => _root_.MartinRoseNichols2025.Examples.ex_24c
  | .ex_25a => _root_.MartinRoseNichols2025.Examples.ex_25a
  | .ex_25b => _root_.MartinRoseNichols2025.Examples.ex_25b
  | .ex_26a => _root_.MartinRoseNichols2025.Examples.ex_26a
  | .ex_26b => _root_.MartinRoseNichols2025.Examples.ex_26b
  | .ex_27a => _root_.MartinRoseNichols2025.Examples.ex_27a
  | .ex_27b => _root_.MartinRoseNichols2025.Examples.ex_27b
  | .ex_33a => _root_.MartinRoseNichols2025.Examples.ex_33a
  | .ex_33b => _root_.MartinRoseNichols2025.Examples.ex_33b
  | .ex_34a => _root_.MartinRoseNichols2025.Examples.ex_34a
  | .ex_34b => _root_.MartinRoseNichols2025.Examples.ex_34b
  | .ex_35a => _root_.MartinRoseNichols2025.Examples.ex_35a
  | .ex_35b => _root_.MartinRoseNichols2025.Examples.ex_35b
  | .ex_36a => _root_.MartinRoseNichols2025.Examples.ex_36a
  | .ex_36b => _root_.MartinRoseNichols2025.Examples.ex_36b
  | .ex_37a => _root_.MartinRoseNichols2025.Examples.ex_37a
  | .ex_37b => _root_.MartinRoseNichols2025.Examples.ex_37b
  | .ex_37c => _root_.MartinRoseNichols2025.Examples.ex_37c
  | .ex_37d => _root_.MartinRoseNichols2025.Examples.ex_37d
  | .ex_38b => _root_.MartinRoseNichols2025.Examples.ex_38b
  | .ex_39a => _root_.MartinRoseNichols2025.Examples.ex_39a
  | .ex_39b => _root_.MartinRoseNichols2025.Examples.ex_39b
  | .ex_40a => _root_.MartinRoseNichols2025.Examples.ex_40a
  | .ex_40b => _root_.MartinRoseNichols2025.Examples.ex_40b
  | .ex_41b => _root_.MartinRoseNichols2025.Examples.ex_41b
  | .ex_42a => _root_.MartinRoseNichols2025.Examples.ex_42a
  | .ex_42b => _root_.MartinRoseNichols2025.Examples.ex_42b
  | .ex_42c => _root_.MartinRoseNichols2025.Examples.ex_42c
  | .ex_42d => _root_.MartinRoseNichols2025.Examples.ex_42d
  | .ex_43a => _root_.MartinRoseNichols2025.Examples.ex_43a
  | .ex_43b => _root_.MartinRoseNichols2025.Examples.ex_43b
  | .ex_43c => _root_.MartinRoseNichols2025.Examples.ex_43c
  | .ex_45a => _root_.MartinRoseNichols2025.Examples.ex_45a
  | .ex_45b => _root_.MartinRoseNichols2025.Examples.ex_45b
  | .ex_46a => _root_.MartinRoseNichols2025.Examples.ex_46a
  | .ex_46b => _root_.MartinRoseNichols2025.Examples.ex_46b
  | .ex_47a => _root_.MartinRoseNichols2025.Examples.ex_47a
  | .ex_47b => _root_.MartinRoseNichols2025.Examples.ex_47b
  | .ex_62a => _root_.MartinRoseNichols2025.Examples.ex_62a
  | .ex_62b => _root_.MartinRoseNichols2025.Examples.ex_62b
  | .ex_62d => _root_.MartinRoseNichols2025.Examples.ex_62d
  | .ex_62e => _root_.MartinRoseNichols2025.Examples.ex_62e
  | .ex_65a => _root_.MartinRoseNichols2025.Examples.ex_65a
  | .ex_65b => _root_.MartinRoseNichols2025.Examples.ex_65b
  | .ex_66a => _root_.MartinRoseNichols2025.Examples.ex_66a
  | .ex_66b => _root_.MartinRoseNichols2025.Examples.ex_66b
  | .ex_78a => _root_.MartinRoseNichols2025.Examples.ex_78a
  | .ex_78b => _root_.MartinRoseNichols2025.Examples.ex_78b
  | .ex_79a => _root_.MartinRoseNichols2025.Examples.ex_79a
  | .ex_79b => _root_.MartinRoseNichols2025.Examples.ex_79b
  | .ex_80a => _root_.MartinRoseNichols2025.Examples.ex_80a
  | .ex_80b => _root_.MartinRoseNichols2025.Examples.ex_80b
  | .ex_80c => _root_.MartinRoseNichols2025.Examples.ex_80c
  | .ex_80d => _root_.MartinRoseNichols2025.Examples.ex_80d
  | .ex_81a => _root_.MartinRoseNichols2025.Examples.ex_81a
  | .ex_81b => _root_.MartinRoseNichols2025.Examples.ex_81b
  | .ex_81c => _root_.MartinRoseNichols2025.Examples.ex_81c
  | .ex_81d => _root_.MartinRoseNichols2025.Examples.ex_81d
  | .ex_96a => _root_.MartinRoseNichols2025.Examples.ex_96a
  | .ex_96b => _root_.MartinRoseNichols2025.Examples.ex_96b

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.MartinRoseNichols2025.Examples.all := rfl

/-- The value the example records under `frame`. -/
def Example.frame : Example → Option Frame
  | .ex_5a => some .periphrastic
  | .ex_5b => some .lexical
  | .ex_6a => some .periphrastic
  | .ex_6b => some .lexical
  | .ex_7a => some .periphrastic
  | .ex_7b => some .lexical
  | .ex_9a => some .lexical
  | .ex_9b => some .lexical
  | .ex_9c => some .lexical
  | .ex_10a => some .lexical
  | .ex_10b => some .lexical
  | .ex_10c => some .lexical
  | .ex_12a => some .lexical
  | .ex_12b => some .lexical
  | .ex_13a => some .lexical
  | .ex_13b => some .periphrastic
  | .ex_13c => some .lexical
  | .ex_14a => some .anticausative
  | .ex_14b => some .lexical
  | .ex_15a => some .anticausative
  | .ex_15b => some .lexical
  | .ex_16a => some .anticausative
  | .ex_16b => some .lexical
  | .ex_18a_damage => some .periphrastic
  | .ex_18a_burn => some .periphrastic
  | .ex_18b_damage => some .lexical
  | .ex_18b_burn => some .lexical
  | .ex_19a_destroy => some .periphrastic
  | .ex_19a_melt => some .periphrastic
  | .ex_19b_destroy => some .lexical
  | .ex_19b_melt => some .lexical
  | .ex_21a => some .periphrastic
  | .ex_21b => some .lexical
  | .ex_22a => some .periphrastic
  | .ex_22b => some .lexical
  | .ex_23a => some .periphrastic
  | .ex_23b => some .lexical
  | .ex_24a => some .lexical
  | .ex_24b => some .lexical
  | .ex_24c => some .lexical
  | .ex_25a => some .periphrastic
  | .ex_25b => some .lexical
  | .ex_26a => some .periphrastic
  | .ex_26b => some .lexical
  | .ex_27a => some .periphrastic
  | .ex_27b => some .lexical
  | .ex_33a => some .periphrastic
  | .ex_33b => some .lexical
  | .ex_34a => some .periphrastic
  | .ex_34b => some .lexical
  | .ex_35a => some .periphrastic
  | .ex_35b => some .lexical
  | .ex_36a => some .periphrastic
  | .ex_36b => some .lexical
  | .ex_37a => some .lexical
  | .ex_37b => some .lexical
  | .ex_37c => some .lexical
  | .ex_37d => some .lexical
  | .ex_38b => some .lexical
  | .ex_39a => some .periphrastic
  | .ex_39b => some .lexical
  | .ex_40a => some .periphrastic
  | .ex_40b => some .lexical
  | .ex_41b => some .lexical
  | .ex_42a => some .lexical
  | .ex_42b => some .periphrastic
  | .ex_42c => some .lexical
  | .ex_42d => some .periphrastic
  | .ex_43a => some .lexical
  | .ex_43b => some .lexical
  | .ex_43c => some .lexical
  | .ex_45a => some .periphrastic
  | .ex_45b => some .lexical
  | .ex_46a => some .periphrastic
  | .ex_46b => some .lexical
  | .ex_47a => some .lexical
  | .ex_47b => some .lexical
  | .ex_62a => some .lexical
  | .ex_62b => some .lexical
  | .ex_62d => some .lexical
  | .ex_62e => some .lexical
  | .ex_65a => some .lexical
  | .ex_65b => some .lexical
  | .ex_66a => some .lexical
  | .ex_66b => some .lexical
  | .ex_78a => some .periphrastic
  | .ex_78b => some .lexical
  | .ex_79a => some .periphrastic
  | .ex_79b => some .lexical
  | .ex_80a => some .periphrastic
  | .ex_80b => some .lexical
  | .ex_80c => some .periphrastic
  | .ex_80d => some .lexical
  | .ex_81a => some .periphrastic
  | .ex_81b => some .lexical
  | .ex_81c => some .periphrastic
  | .ex_81d => some .lexical
  | .ex_96a => some .lexical
  | .ex_96b => some .lexical

theorem Example.frame_datum :
    ∀ x : Example, _root_.MartinRoseNichols2025.Examples.frame x.datum = x.frame := by
  decide +kernel

/-- The value the example records under `sense`. -/
def Example.sense : Example → Option Sense
  | .ex_5a => some .physical
  | .ex_5b => some .physical
  | .ex_6a => some .physical
  | .ex_6b => some .physical
  | .ex_7a => some .physical
  | .ex_7b => some .physical
  | .ex_9a => some .abstract
  | .ex_9b => some .abstract
  | .ex_9c => some .abstract
  | .ex_10a => some .physical
  | .ex_10b => some .physical
  | .ex_10c => some .physical
  | .ex_12a => some .physical
  | .ex_12b => some .physical
  | .ex_13a => some .physical
  | .ex_13b => some .physical
  | .ex_13c => some .abstract
  | .ex_14a => some .physical
  | .ex_14b => some .physical
  | .ex_15a => some .physical
  | .ex_15b => some .physical
  | .ex_16a => some .physical
  | .ex_16b => some .physical
  | .ex_18a_damage => some .physical
  | .ex_18a_burn => some .physical
  | .ex_18b_damage => some .physical
  | .ex_18b_burn => some .physical
  | .ex_19a_destroy => some .physical
  | .ex_19a_melt => some .physical
  | .ex_19b_destroy => some .physical
  | .ex_19b_melt => some .physical
  | .ex_21a => some .physical
  | .ex_21b => some .physical
  | .ex_22a => some .physical
  | .ex_22b => some .physical
  | .ex_23a => some .physical
  | .ex_23b => some .physical
  | .ex_24a => some .abstract
  | .ex_24b => some .abstract
  | .ex_24c => some .abstract
  | .ex_25a => some .physical
  | .ex_25b => some .physical
  | .ex_26a => some .physical
  | .ex_26b => some .physical
  | .ex_27a => some .physical
  | .ex_27b => some .physical
  | .ex_33a => some .physical
  | .ex_33b => some .physical
  | .ex_34a => some .physical
  | .ex_34b => some .physical
  | .ex_35a => some .physical
  | .ex_35b => some .physical
  | .ex_36a => some .physical
  | .ex_36b => some .physical
  | .ex_37a => some .abstract
  | .ex_37b => some .abstract
  | .ex_37c => some .abstract
  | .ex_37d => some .abstract
  | .ex_38b => some .physical
  | .ex_39a => some .physical
  | .ex_39b => some .physical
  | .ex_40a => some .physical
  | .ex_40b => some .physical
  | .ex_41b => some .physical
  | .ex_42a => some .physical
  | .ex_42b => some .physical
  | .ex_42c => some .physical
  | .ex_42d => some .physical
  | .ex_43a => some .physical
  | .ex_43b => some .physical
  | .ex_43c => some .physical
  | .ex_45a => some .physical
  | .ex_45b => some .physical
  | .ex_46a => some .physical
  | .ex_46b => some .physical
  | .ex_47a => some .physical
  | .ex_47b => some .physical
  | .ex_62a => some .physical
  | .ex_62b => some .physical
  | .ex_62d => some .physical
  | .ex_62e => some .physical
  | .ex_65a => some .physical
  | .ex_65b => some .physical
  | .ex_66a => some .physical
  | .ex_66b => some .physical
  | .ex_78a => some .physical
  | .ex_78b => some .physical
  | .ex_79a => some .physical
  | .ex_79b => some .physical
  | .ex_80a => some .physical
  | .ex_80b => some .physical
  | .ex_80c => some .physical
  | .ex_80d => some .physical
  | .ex_81a => some .physical
  | .ex_81b => some .physical
  | .ex_81c => some .physical
  | .ex_81d => some .physical
  | .ex_96a => some .physical
  | .ex_96b => some .physical

theorem Example.sense_datum :
    ∀ x : Example, _root_.MartinRoseNichols2025.Examples.sense x.datum = x.sense := by
  decide +kernel

/-- The value the example records under `subject`. -/
def Example.subject : Example → Option Subject
  | .ex_5a => some .absence
  | .ex_5b => some .absence
  | .ex_6a => some .absence
  | .ex_6b => some .absence
  | .ex_7a => some .absence
  | .ex_7b => some .absence
  | .ex_9a => some .absence
  | .ex_9b => some .absence
  | .ex_9c => some .absence
  | .ex_10a => some .absence
  | .ex_10b => some .absence
  | .ex_10c => some .absence
  | .ex_12a => some .absence
  | .ex_12b => some .absence
  | .ex_13a => some .absence
  | .ex_13b => some .absence
  | .ex_13c => some .absence
  | .ex_14a => some .absence
  | .ex_14b => some .absence
  | .ex_15a => some .absence
  | .ex_15b => some .absence
  | .ex_16a => some .absence
  | .ex_16b => some .absence
  | .ex_18a_damage => some .fact
  | .ex_18a_burn => some .fact
  | .ex_18b_damage => some .fact
  | .ex_18b_burn => some .fact
  | .ex_19a_destroy => some .fact
  | .ex_19a_melt => some .fact
  | .ex_19b_destroy => some .fact
  | .ex_19b_melt => some .fact
  | .ex_21a => some .gerund
  | .ex_21b => some .gerund
  | .ex_22a => some .gerund
  | .ex_22b => some .gerund
  | .ex_23a => some .gerund
  | .ex_23b => some .gerund
  | .ex_24a => some .gerund
  | .ex_24b => some .gerund
  | .ex_24c => some .gerund
  | .ex_25a => some .gerund
  | .ex_25b => some .gerund
  | .ex_26a => some .gerund
  | .ex_26b => some .gerund
  | .ex_27a => some .gerund
  | .ex_27b => some .gerund
  | .ex_33a => some .degree
  | .ex_33b => some .degree
  | .ex_34a => some .degree
  | .ex_34b => some .degree
  | .ex_35a => some .degree
  | .ex_35b => some .degree
  | .ex_36a => some .degree
  | .ex_36b => some .degree
  | .ex_37a => some .degree
  | .ex_37b => some .degree
  | .ex_37c => some .degree
  | .ex_37d => some .degree
  | .ex_38b => some .degree
  | .ex_39a => some .degree
  | .ex_39b => some .degree
  | .ex_40a => some .degree
  | .ex_40b => some .degree
  | .ex_41b => some .degree
  | .ex_42a => some .event
  | .ex_42b => some .event
  | .ex_42c => some .event
  | .ex_42d => some .event
  | .ex_43a => some .event
  | .ex_43b => some .event
  | .ex_43c => some .event
  | .ex_45a => some .event
  | .ex_45b => some .event
  | .ex_46a => some .event
  | .ex_46b => some .event
  | .ex_47a => some .event
  | .ex_47b => some .event
  | .ex_62a => some .absence
  | .ex_62b => some .absence
  | .ex_62d => some .absence
  | .ex_62e => some .absence
  | .ex_65a => some .fact
  | .ex_65b => some .fact
  | .ex_66a => some .degree
  | .ex_66b => some .degree
  | .ex_78a => some .individual
  | .ex_78b => some .individual
  | .ex_79a => some .individual
  | .ex_79b => some .individual
  | .ex_80a => some .individual
  | .ex_80b => some .individual
  | .ex_80c => some .individual
  | .ex_80d => some .individual
  | .ex_81a => some .individual
  | .ex_81b => some .individual
  | .ex_81c => some .individual
  | .ex_81d => some .individual
  | .ex_96a => some .absence
  | .ex_96b => some .absence

theorem Example.subject_datum :
    ∀ x : Example, _root_.MartinRoseNichols2025.Examples.subject x.datum = x.subject := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_5a => [(.verb, .burn)]
  | .ex_5b => [(.verb, .burn)]
  | .ex_6a => [(.verb, .melt)]
  | .ex_6b => [(.verb, .melt)]
  | .ex_7a => [(.verb, .flood)]
  | .ex_7b => [(.verb, .flood)]
  | .ex_9a => [(.verb, .burn)]
  | .ex_9b => [(.verb, .melt)]
  | .ex_9c => [(.verb, .flood)]
  | .ex_10a => [(.verb, .kill)]
  | .ex_10b => [(.verb, .damage)]
  | .ex_10c => [(.verb, .trigger)]
  | .ex_12a => [(.verb, .change)]
  | .ex_12b => [(.verb, .activate)]
  | .ex_13a => [(.verb, .bury)]
  | .ex_13b => [(.verb, .bury)]
  | .ex_13c => [(.verb, .bury)]
  | .ex_14a => [(.verb, .burn)]
  | .ex_14b => [(.verb, .burn)]
  | .ex_15a => [(.verb, .break)]
  | .ex_15b => [(.verb, .break)]
  | .ex_16a => [(.verb, .crack)]
  | .ex_16b => [(.verb, .crack)]
  | .ex_18a_damage => [(.verb, .damage)]
  | .ex_18a_burn => [(.verb, .burn)]
  | .ex_18b_damage => [(.verb, .damage)]
  | .ex_18b_burn => [(.verb, .burn)]
  | .ex_19a_destroy => [(.verb, .destroy)]
  | .ex_19a_melt => [(.verb, .melt)]
  | .ex_19b_destroy => [(.verb, .destroy)]
  | .ex_19b_melt => [(.verb, .melt)]
  | .ex_21a => [(.verb, .burn)]
  | .ex_21b => [(.verb, .burn)]
  | .ex_22a => [(.verb, .melt)]
  | .ex_22b => [(.verb, .melt)]
  | .ex_23a => [(.verb, .flood)]
  | .ex_23b => [(.verb, .flood)]
  | .ex_24a => [(.verb, .burn)]
  | .ex_24b => [(.verb, .melt)]
  | .ex_24c => [(.verb, .flood)]
  | .ex_25a => [(.verb, .damage)]
  | .ex_25b => [(.verb, .damage)]
  | .ex_26a => [(.verb, .die)]
  | .ex_26b => [(.verb, .kill)]
  | .ex_27a => [(.verb, .trigger)]
  | .ex_27b => [(.verb, .trigger)]
  | .ex_33a => [(.verb, .burn)]
  | .ex_33b => [(.verb, .burn)]
  | .ex_34a => [(.verb, .melt)]
  | .ex_34b => [(.verb, .melt)]
  | .ex_35a => [(.verb, .bury)]
  | .ex_35b => [(.verb, .bury)]
  | .ex_36a => [(.verb, .flood)]
  | .ex_36b => [(.verb, .flood)]
  | .ex_37a => [(.verb, .burn)]
  | .ex_37b => [(.verb, .melt)]
  | .ex_37c => [(.verb, .flood)]
  | .ex_37d => [(.verb, .bury)]
  | .ex_38b => [(.verb, .damage)]
  | .ex_39a => [(.verb, .trigger)]
  | .ex_39b => [(.verb, .trigger)]
  | .ex_40a => [(.verb, .die)]
  | .ex_40b => [(.verb, .kill)]
  | .ex_41b => [(.verb, .change)]
  | .ex_42a => [(.verb, .break)]
  | .ex_42b => [(.verb, .break)]
  | .ex_42c => [(.verb, .boil)]
  | .ex_42d => [(.verb, .boil)]
  | .ex_43a => [(.verb, .break)]
  | .ex_43b => [(.verb, .burn)]
  | .ex_43c => [(.verb, .boil)]
  | .ex_45a => [(.verb, .burn)]
  | .ex_45b => [(.verb, .burn)]
  | .ex_46a => [(.verb, .flood)]
  | .ex_46b => [(.verb, .flood)]
  | .ex_47a => [(.verb, .destroy)]
  | .ex_47b => [(.verb, .change)]
  | .ex_62a => [(.verb, .burn)]
  | .ex_62b => [(.verb, .burn)]
  | .ex_62d => [(.verb, .lift)]
  | .ex_62e => [(.verb, .lock)]
  | .ex_65a => [(.verb, .crack)]
  | .ex_65b => [(.verb, .destroy)]
  | .ex_66a => [(.verb, .melt)]
  | .ex_66b => [(.verb, .lift)]
  | .ex_78a => [(.verb, .crack)]
  | .ex_78b => [(.verb, .crack)]
  | .ex_79a => [(.verb, .damage)]
  | .ex_79b => [(.verb, .damage)]
  | .ex_80a => [(.verb, .crash)]
  | .ex_80b => [(.verb, .crash)]
  | .ex_80c => [(.verb, .destroy)]
  | .ex_80d => [(.verb, .destroy)]
  | .ex_81a => [(.verb, .heat)]
  | .ex_81b => [(.verb, .heat)]
  | .ex_81c => [(.verb, .ruin)]
  | .ex_81d => [(.verb, .ruin)]
  | .ex_96a => [(.verb, .lower)]
  | .ex_96b => [(.verb, .drop)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.MartinRoseNichols2025.Examples.label? · = some l)).filterMap _root_.MartinRoseNichols2025.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end MartinRoseNichols2025.Examples
