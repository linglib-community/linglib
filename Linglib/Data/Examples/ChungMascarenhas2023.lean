module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `ChungMascarenhas2023` — typed example data

Auto-generated from `Linglib/Data/Examples/ChungMascarenhas2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChungMascarenhas2023.Examples`.
-/

@[expose] public section

namespace ChungMascarenhas2023.Examples

def ex_1 : Datum :=
  { id := "chungmascarenhas2023_1"
    source := ⟨"chung-mascarenhas-2023", "(1), (42)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "John-un cip-ey iss-∅-eya toy-n-ta."
    glossedTokens := [("John-un", "John-TOP"), ("cip-ey", "home-DAT"), ("iss-∅-eya", "COP-PRES-only.if"), ("toy-n-ta", "EVAL-PRES-DECL")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'u', 'n'], ['J', 'o', 'h', 'n', '-', 'T', 'O', 'P'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['u', 'n'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['c', 'i', 'p', '-', 'e', 'y'], ['h', 'o', 'm', 'e', '-', 'D', 'A', 'T'], [⟨['c', 'i', 'p'], ['h', 'o', 'm', 'e'], none⟩, ⟨['e', 'y'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['i', 's', 's', '-', '∅', '-', 'e', 'y', 'a'], ['C', 'O', 'P', '-', 'P', 'R', 'E', 'S', '-', 'o', 'n', 'l', 'y', '.', 'i', 'f'], [⟨['i', 's', 's'], ['C', 'O', 'P'], none⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['e', 'y', 'a'], ['o', 'n', 'l', 'y', '.', 'i', 'f'], some '-'⟩]⟩, ⟨['t', 'o', 'y', '-', 'n', '-', 't', 'a'], ['E', 'V', 'A', 'L', '-', 'P', 'R', 'E', 'S', '-', 'D', 'E', 'C', 'L'], [⟨['t', 'o', 'y'], ['E', 'V', 'A', 'L'], none⟩, ⟨['n'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['t', 'a'], ['D', 'E', 'C', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_15a : Datum :=
  { id := "chungmascarenhas2023_15a"
    source := ⟨"kolodny-macfarlane-2010", "Miners puzzle"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(15a)"⟩
    language := "stan1293"
    primaryText := "We ought to block neither shaft."
    glossedTokens := [("We", ""), ("ought", ""), ("to", ""), ("block", ""), ("neither", ""), ("shaft", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['o', 'u', 'g', 'h', 't'], [], [⟨['o', 'u', 'g', 'h', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['n', 'e', 'i', 't', 'h', 'e', 'r'], [], [⟨['n', 'e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨1, 1, "modal", some "ought"⟩]
    paperFeatures := [("prejacent", "block-neither")] }

def ex_15b : Datum :=
  { id := "chungmascarenhas2023_15b"
    source := ⟨"kolodny-macfarlane-2010", "Miners puzzle"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(15b)"⟩
    language := "stan1293"
    primaryText := "If the miners are in shaft A, we ought to block shaft A."
    glossedTokens := [("If", ""), ("the", ""), ("miners", ""), ("are", ""), ("in", ""), ("shaft", ""), ("A,", ""), ("we", ""), ("ought", ""), ("to", ""), ("block", ""), ("shaft", ""), ("A", "")]
    glossedWords := [⟨['I', 'f'], [], [⟨['I', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'e', 'r', 's'], [], [⟨['m', 'i', 'n', 'e', 'r', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['A', ','], [], [⟨['A'], [], none⟩]⟩, ⟨['w', 'e'], [], [⟨['w', 'e'], [], none⟩]⟩, ⟨['o', 'u', 'g', 'h', 't'], [], [⟨['o', 'u', 'g', 'h', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['A'], [], [⟨['A'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨8, 1, "modal", some "ought"⟩]
    paperFeatures := [("prejacent", "block-A"), ("antecedent", "miners-in-A")] }

def ex_15c : Datum :=
  { id := "chungmascarenhas2023_15c"
    source := ⟨"kolodny-macfarlane-2010", "Miners puzzle"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(15c)"⟩
    language := "stan1293"
    primaryText := "If the miners are in shaft B, we ought to block shaft B."
    glossedTokens := [("If", ""), ("the", ""), ("miners", ""), ("are", ""), ("in", ""), ("shaft", ""), ("B,", ""), ("we", ""), ("ought", ""), ("to", ""), ("block", ""), ("shaft", ""), ("B", "")]
    glossedWords := [⟨['I', 'f'], [], [⟨['I', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'e', 'r', 's'], [], [⟨['m', 'i', 'n', 'e', 'r', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['B', ','], [], [⟨['B'], [], none⟩]⟩, ⟨['w', 'e'], [], [⟨['w', 'e'], [], none⟩]⟩, ⟨['o', 'u', 'g', 'h', 't'], [], [⟨['o', 'u', 'g', 'h', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['B'], [], [⟨['B'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨8, 1, "modal", some "ought"⟩]
    paperFeatures := [("prejacent", "block-B"), ("antecedent", "miners-in-B")] }

def ex_25a : Datum :=
  { id := "chungmascarenhas2023_25a"
    source := ⟨"chung-mascarenhas-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We must block neither path."
    glossedTokens := [("We", ""), ("must", ""), ("block", ""), ("neither", ""), ("path", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['n', 'e', 'i', 't', 'h', 'e', 'r'], [], [⟨['n', 'e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 't', 'h'], [], [⟨['p', 'a', 't', 'h'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "modal", some "must"⟩]
    paperFeatures := [("prejacent", "block-neither")] }

def ex_25a_have_to : Datum :=
  { id := "chungmascarenhas2023_25a_have_to"
    source := ⟨"chung-mascarenhas-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We have to block neither path."
    glossedTokens := [("We", ""), ("have", ""), ("to", ""), ("block", ""), ("neither", ""), ("path", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['n', 'e', 'i', 't', 'h', 'e', 'r'], [], [⟨['n', 'e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 't', 'h'], [], [⟨['p', 'a', 't', 'h'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 2, "modal", none⟩]
    paperFeatures := [("prejacent", "block-neither")] }

def ex_25b : Datum :=
  { id := "chungmascarenhas2023_25b"
    source := ⟨"chung-mascarenhas-2023", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the miners are in shaft A, we must block shaft A."
    glossedTokens := [("If", ""), ("the", ""), ("miners", ""), ("are", ""), ("in", ""), ("shaft", ""), ("A,", ""), ("we", ""), ("must", ""), ("block", ""), ("shaft", ""), ("A", "")]
    glossedWords := [⟨['I', 'f'], [], [⟨['I', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'e', 'r', 's'], [], [⟨['m', 'i', 'n', 'e', 'r', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['A', ','], [], [⟨['A'], [], none⟩]⟩, ⟨['w', 'e'], [], [⟨['w', 'e'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['A'], [], [⟨['A'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨8, 1, "modal", some "must"⟩]
    paperFeatures := [("prejacent", "block-A"), ("antecedent", "miners-in-A")] }

def ex_25b_have_to : Datum :=
  { id := "chungmascarenhas2023_25b_have_to"
    source := ⟨"chung-mascarenhas-2023", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the miners are in shaft A, we have to block shaft A."
    glossedTokens := [("If", ""), ("the", ""), ("miners", ""), ("are", ""), ("in", ""), ("shaft", ""), ("A,", ""), ("we", ""), ("have", ""), ("to", ""), ("block", ""), ("shaft", ""), ("A", "")]
    glossedWords := [⟨['I', 'f'], [], [⟨['I', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'e', 'r', 's'], [], [⟨['m', 'i', 'n', 'e', 'r', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['A', ','], [], [⟨['A'], [], none⟩]⟩, ⟨['w', 'e'], [], [⟨['w', 'e'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['A'], [], [⟨['A'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨8, 2, "modal", none⟩]
    paperFeatures := [("prejacent", "block-A"), ("antecedent", "miners-in-A")] }

def ex_25c : Datum :=
  { id := "chungmascarenhas2023_25c"
    source := ⟨"chung-mascarenhas-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the miners are in shaft B, we must block shaft B."
    glossedTokens := [("If", ""), ("the", ""), ("miners", ""), ("are", ""), ("in", ""), ("shaft", ""), ("B,", ""), ("we", ""), ("must", ""), ("block", ""), ("shaft", ""), ("B", "")]
    glossedWords := [⟨['I', 'f'], [], [⟨['I', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'e', 'r', 's'], [], [⟨['m', 'i', 'n', 'e', 'r', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['B', ','], [], [⟨['B'], [], none⟩]⟩, ⟨['w', 'e'], [], [⟨['w', 'e'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['B'], [], [⟨['B'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨8, 1, "modal", some "must"⟩]
    paperFeatures := [("prejacent", "block-B"), ("antecedent", "miners-in-B")] }

def ex_25c_have_to : Datum :=
  { id := "chungmascarenhas2023_25c_have_to"
    source := ⟨"chung-mascarenhas-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the miners are in shaft B, we have to block shaft B."
    glossedTokens := [("If", ""), ("the", ""), ("miners", ""), ("are", ""), ("in", ""), ("shaft", ""), ("B,", ""), ("we", ""), ("have", ""), ("to", ""), ("block", ""), ("shaft", ""), ("B", "")]
    glossedWords := [⟨['I', 'f'], [], [⟨['I', 'f'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'i', 'n', 'e', 'r', 's'], [], [⟨['m', 'i', 'n', 'e', 'r', 's'], [], none⟩]⟩, ⟨['a', 'r', 'e'], [], [⟨['a', 'r', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['B', ','], [], [⟨['B'], [], none⟩]⟩, ⟨['w', 'e'], [], [⟨['w', 'e'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'f', 't'], [], [⟨['s', 'h', 'a', 'f', 't'], [], none⟩]⟩, ⟨['B'], [], [⟨['B'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨8, 2, "modal", none⟩]
    paperFeatures := [("prejacent", "block-B"), ("antecedent", "miners-in-B")] }

def ex_26a : Datum :=
  { id := "chungmascarenhas2023_26a"
    source := ⟨"chung-mascarenhas-2023", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We mustn't block either path."
    glossedTokens := [("We", ""), ("mustn't", ""), ("block", ""), ("either", ""), ("path", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['m', 'u', 's', 't', 'n', '\'', 't'], [], [⟨['m', 'u', 's', 't', 'n', '\'', 't'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 't', 'h'], [], [⟨['p', 'a', 't', 'h'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_26b : Datum :=
  { id := "chungmascarenhas2023_26b"
    source := ⟨"chung-mascarenhas-2023", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We must refrain from blocking either path."
    glossedTokens := [("We", ""), ("must", ""), ("refrain", ""), ("from", ""), ("blocking", ""), ("either", ""), ("path", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['r', 'e', 'f', 'r', 'a', 'i', 'n'], [], [⟨['r', 'e', 'f', 'r', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], [⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 't', 'h'], [], [⟨['p', 'a', 't', 'h'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨1, 1, "modal", some "must"⟩]
    paperFeatures := [("prejacent", "block-neither")] }

def ex_26b_have_to : Datum :=
  { id := "chungmascarenhas2023_26b_have_to"
    source := ⟨"chung-mascarenhas-2023", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We have to refrain from blocking either path."
    glossedTokens := [("We", ""), ("have", ""), ("to", ""), ("refrain", ""), ("from", ""), ("blocking", ""), ("either", ""), ("path", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['r', 'e', 'f', 'r', 'a', 'i', 'n'], [], [⟨['r', 'e', 'f', 'r', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], [⟨['b', 'l', 'o', 'c', 'k', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 't', 'h'], [], [⟨['p', 'a', 't', 'h'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨1, 2, "modal", none⟩]
    paperFeatures := [("prejacent", "block-neither")] }

def ex_26c : Datum :=
  { id := "chungmascarenhas2023_26c"
    source := ⟨"chung-mascarenhas-2023", "(26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We cannot block either path."
    glossedTokens := [("We", ""), ("cannot", ""), ("block", ""), ("either", ""), ("path", "")]
    glossedWords := [⟨['W', 'e'], [], [⟨['W', 'e'], [], none⟩]⟩, ⟨['c', 'a', 'n', 'n', 'o', 't'], [], [⟨['c', 'a', 'n', 'n', 'o', 't'], [], none⟩]⟩, ⟨['b', 'l', 'o', 'c', 'k'], [], [⟨['b', 'l', 'o', 'c', 'k'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['p', 'a', 't', 'h'], [], [⟨['p', 'a', 't', 'h'], [], none⟩]⟩]
    context := "Ten miners are trapped either in shaft A or in shaft B, but we do not know which. Flood waters threaten to flood the shafts. We have enough sandbags to block one shaft, but not both. If we block one shaft, all the water will go into the other shaft, killing any miners inside it. If we block neither shaft, both shafts will fill halfway with water, and just one miner, the lowest in the shaft, will be killed."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_29a : Datum :=
  { id := "chungmascarenhas2023_29a"
    source := ⟨"chung-mascarenhas-2023", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Linda must be a bank teller."
    glossedTokens := [("Linda", ""), ("must", ""), ("be", ""), ("a", ""), ("bank", ""), ("teller", "")]
    glossedWords := [⟨['L', 'i', 'n', 'd', 'a'], [], [⟨['L', 'i', 'n', 'd', 'a'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['b', 'a', 'n', 'k'], [], [⟨['b', 'a', 'n', 'k'], [], none⟩]⟩, ⟨['t', 'e', 'l', 'l', 'e', 'r'], [], [⟨['t', 'e', 'l', 'l', 'e', 'r'], [], none⟩]⟩]
    context := "Linda is 31 years old, single, outspoken, and very bright. She majored in philosophy. As a student, she was deeply concerned with issues of discrimination and social justice, and also participated in anti-nuclear demonstrations."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_29b : Datum :=
  { id := "chungmascarenhas2023_29b"
    source := ⟨"chung-mascarenhas-2023", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Linda must be a bank teller and be active in the feminist movement."
    glossedTokens := [("Linda", ""), ("must", ""), ("be", ""), ("a", ""), ("bank", ""), ("teller", ""), ("and", ""), ("be", ""), ("active", ""), ("in", ""), ("the", ""), ("feminist", ""), ("movement", "")]
    glossedWords := [⟨['L', 'i', 'n', 'd', 'a'], [], [⟨['L', 'i', 'n', 'd', 'a'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['b', 'a', 'n', 'k'], [], [⟨['b', 'a', 'n', 'k'], [], none⟩]⟩, ⟨['t', 'e', 'l', 'l', 'e', 'r'], [], [⟨['t', 'e', 'l', 'l', 'e', 'r'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a', 'c', 't', 'i', 'v', 'e'], [], [⟨['a', 'c', 't', 'i', 'v', 'e'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['f', 'e', 'm', 'i', 'n', 'i', 's', 't'], [], [⟨['f', 'e', 'm', 'i', 'n', 'i', 's', 't'], [], none⟩]⟩, ⟨['m', 'o', 'v', 'e', 'm', 'e', 'n', 't'], [], [⟨['m', 'o', 'v', 'e', 'm', 'e', 'n', 't'], [], none⟩]⟩]
    context := "Linda is 31 years old, single, outspoken, and very bright. She majored in philosophy. As a student, she was deeply concerned with issues of discrimination and social justice, and also participated in anti-nuclear demonstrations."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_36 : Datum :=
  { id := "chungmascarenhas2023_36"
    source := ⟨"chung-mascarenhas-2023", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jack must be an engineer."
    glossedTokens := [("Jack", ""), ("must", ""), ("be", ""), ("an", ""), ("engineer", "")]
    glossedWords := [⟨['J', 'a', 'c', 'k'], [], [⟨['J', 'a', 'c', 'k'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a', 'n'], [], [⟨['a', 'n'], [], none⟩]⟩, ⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r'], [], [⟨['e', 'n', 'g', 'i', 'n', 'e', 'e', 'r'], [], none⟩]⟩]
    context := "A panel of psychologists have interviewed and administered personality tests to 30 engineers and 70 lawyers. On the basis of this information, thumbnail descriptions of the 30 engineers and 70 lawyers have been written. Below is the thumbnail description of Jack, one of the interviewees: Jack is a 45-year-old man. He is married and has four children. He is generally conservative, careful, and ambitious. He shows no interest in political and social issues and spends most of his free time on his many hobbies which include home carpentry, sailing, and mathematical puzzles."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_49a : Datum :=
  { id := "chungmascarenhas2023_49a"
    source := ⟨"chung-mascarenhas-2023", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did not come to work today. He must have caught a cold."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_49b : Datum :=
  { id := "chungmascarenhas2023_49b"
    source := ⟨"chung-mascarenhas-2023", "(49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did not come to work today. He must be dead."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_54a : Datum :=
  { id := "chungmascarenhas2023_54a"
    source := ⟨"chung-mascarenhas-2023", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "One must under no circumstance ever make a grammatical mistake."
    glossedTokens := [("One", ""), ("must", ""), ("under", ""), ("no", ""), ("circumstance", ""), ("ever", ""), ("make", ""), ("a", ""), ("grammatical", ""), ("mistake", "")]
    glossedWords := [⟨['O', 'n', 'e'], [], [⟨['O', 'n', 'e'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['u', 'n', 'd', 'e', 'r'], [], [⟨['u', 'n', 'd', 'e', 'r'], [], none⟩]⟩, ⟨['n', 'o'], [], [⟨['n', 'o'], [], none⟩]⟩, ⟨['c', 'i', 'r', 'c', 'u', 'm', 's', 't', 'a', 'n', 'c', 'e'], [], [⟨['c', 'i', 'r', 'c', 'u', 'm', 's', 't', 'a', 'n', 'c', 'e'], [], none⟩]⟩, ⟨['e', 'v', 'e', 'r'], [], [⟨['e', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['m', 'a', 'k', 'e'], [], [⟨['m', 'a', 'k', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['g', 'r', 'a', 'm', 'm', 'a', 't', 'i', 'c', 'a', 'l'], [], [⟨['g', 'r', 'a', 'm', 'm', 'a', 't', 'i', 'c', 'a', 'l'], [], none⟩]⟩, ⟨['m', 'i', 's', 't', 'a', 'k', 'e'], [], [⟨['m', 'i', 's', 't', 'a', 'k', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_55a : Datum :=
  { id := "chungmascarenhas2023_55a"
    source := ⟨"chung-mascarenhas-2023", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In order to get to Bushwick, you have to take a helicopter."
    glossedTokens := [("In", ""), ("order", ""), ("to", ""), ("get", ""), ("to", ""), ("Bushwick,", ""), ("you", ""), ("have", ""), ("to", ""), ("take", ""), ("a", ""), ("helicopter", "")]
    glossedWords := [⟨['I', 'n'], [], [⟨['I', 'n'], [], none⟩]⟩, ⟨['o', 'r', 'd', 'e', 'r'], [], [⟨['o', 'r', 'd', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['g', 'e', 't'], [], [⟨['g', 'e', 't'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['B', 'u', 's', 'h', 'w', 'i', 'c', 'k', ','], [], [⟨['B', 'u', 's', 'h', 'w', 'i', 'c', 'k'], [], none⟩]⟩, ⟨['y', 'o', 'u'], [], [⟨['y', 'o', 'u'], [], none⟩]⟩, ⟨['h', 'a', 'v', 'e'], [], [⟨['h', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['t', 'a', 'k', 'e'], [], [⟨['t', 'a', 'k', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['h', 'e', 'l', 'i', 'c', 'o', 'p', 't', 'e', 'r'], [], [⟨['h', 'e', 'l', 'i', 'c', 'o', 'p', 't', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_60a : Datum :=
  { id := "chungmascarenhas2023_60a"
    source := ⟨"chung-mascarenhas-2023", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim must marry Pat in order to inherit."
    glossedTokens := [("Kim", ""), ("must", ""), ("marry", ""), ("Pat", ""), ("in", ""), ("order", ""), ("to", ""), ("inherit", "")]
    glossedWords := [⟨['K', 'i', 'm'], [], [⟨['K', 'i', 'm'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['m', 'a', 'r', 'r', 'y'], [], [⟨['m', 'a', 'r', 'r', 'y'], [], none⟩]⟩, ⟨['P', 'a', 't'], [], [⟨['P', 'a', 't'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['o', 'r', 'd', 'e', 'r'], [], [⟨['o', 'r', 'd', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['i', 'n', 'h', 'e', 'r', 'i', 't'], [], [⟨['i', 'n', 'h', 'e', 'r', 'i', 't'], [], none⟩]⟩]
    context := "Kim will only inherit the considerable fortune their parents left them if they get married. They can marry anyone they like, the condition is simply that Kim be married in order to inherit. Suppose Kim is planning on marrying Pat."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    spans := [⟨1, 1, "modal", some "must"⟩]
    paperFeatures := [] }

def ex_60b : Datum :=
  { id := "chungmascarenhas2023_60b"
    source := ⟨"chung-mascarenhas-2023", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim must marry PAT in order to inherit."
    glossedTokens := [("Kim", ""), ("must", ""), ("marry", ""), ("PAT", ""), ("in", ""), ("order", ""), ("to", ""), ("inherit", "")]
    glossedWords := [⟨['K', 'i', 'm'], [], [⟨['K', 'i', 'm'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['m', 'a', 'r', 'r', 'y'], [], [⟨['m', 'a', 'r', 'r', 'y'], [], none⟩]⟩, ⟨['P', 'A', 'T'], [], [⟨['P', 'A', 'T'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['o', 'r', 'd', 'e', 'r'], [], [⟨['o', 'r', 'd', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['i', 'n', 'h', 'e', 'r', 'i', 't'], [], [⟨['i', 'n', 'h', 'e', 'r', 'i', 't'], [], none⟩]⟩]
    context := "Kim will only inherit the considerable fortune their parents left them if they get married. They can marry anyone they like, the condition is simply that Kim be married in order to inherit. Suppose Kim is planning on marrying Pat."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    spans := [⟨1, 1, "modal", some "must"⟩]
    paperFeatures := [("focus", "Pat")] }

def ex_63 : Datum :=
  { id := "chungmascarenhas2023_63"
    source := ⟨"von-fintel-gillies-2010", "(6b)"⟩
    reportedIn := some ⟨"chung-mascarenhas-2023", "(63)"⟩
    language := "stan1293"
    primaryText := "It must be raining."
    glossedTokens := [("It", ""), ("must", ""), ("be", ""), ("raining", "")]
    glossedWords := [⟨['I', 't'], [], [⟨['I', 't'], [], none⟩]⟩, ⟨['m', 'u', 's', 't'], [], [⟨['m', 'u', 's', 't'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['r', 'a', 'i', 'n', 'i', 'n', 'g'], [], [⟨['r', 'a', 'i', 'n', 'i', 'n', 'g'], [], none⟩]⟩]
    context := "Billy is looking out the window at the pouring rain."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1, ex_15a, ex_15b, ex_15c, ex_25a, ex_25a_have_to, ex_25b, ex_25b_have_to, ex_25c, ex_25c_have_to, ex_26a, ex_26b, ex_26b_have_to, ex_26c, ex_29a, ex_29b, ex_36, ex_49a, ex_49b, ex_54a, ex_55a, ex_60a, ex_60b, ex_63]

/-- The action a sentence of the miners puzzle is about, under the paper's name for the proposition. -/
inductive Prejacent where
  /-- block-neither: we block neither shaft -/
  | blockNeither
  /-- block-A: we block shaft A -/
  | blockA
  /-- block-B: we block shaft B -/
  | blockB
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `prejacent`. -/
def prejacent (e : Datum) : Option Prejacent :=
  e.parse? "prejacent" [("block-neither", .blockNeither), ("block-A", .blockA), ("block-B", .blockB)]

/-- The if-clause of a sentence of the miners puzzle, under the paper's name for the proposition. -/
inductive Antecedent where
  /-- miners-in-A: the miners are in shaft A -/
  | minersInA
  /-- miners-in-B: the miners are in shaft B -/
  | minersInB
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `antecedent`. -/
def antecedent (e : Datum) : Option Antecedent :=
  e.parse? "antecedent" [("miners-in-A", .minersInA), ("miners-in-B", .minersInB)]

/-- The focused constituent of the prejacent, where the paper marks one. -/
inductive Focus where
  /-- Pat: focus on the object *Pat* -/
  | pat
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `focus`. -/
def focus (e : Datum) : Option Focus :=
  e.parse? "focus" [("Pat", .pat)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- modal: the necessity modal under test -/
  | modal
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("modal", .modal)]

/-- The modal auxiliaries under test. -/
inductive Lexeme where
  /-- must: English *must* -/
  | must
  /-- ought: English *ought* -/
  | ought
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("must", .must), ("ought", .ought)])

/-- The examples of the article. -/
inductive Example where
  | ex_1
  | ex_15a
  | ex_15b
  | ex_15c
  | ex_25a
  | ex_25a_have_to
  | ex_25b
  | ex_25b_have_to
  | ex_25c
  | ex_25c_have_to
  | ex_26a
  | ex_26b
  | ex_26b_have_to
  | ex_26c
  | ex_29a
  | ex_29b
  | ex_36
  | ex_49a
  | ex_49b
  | ex_54a
  | ex_55a
  | ex_60a
  | ex_60b
  | ex_63
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_1, .ex_15a, .ex_15b, .ex_15c, .ex_25a, .ex_25a_have_to, .ex_25b, .ex_25b_have_to, .ex_25c,
    .ex_25c_have_to, .ex_26a, .ex_26b, .ex_26b_have_to, .ex_26c, .ex_29a, .ex_29b, .ex_36,
    .ex_49a, .ex_49b, .ex_54a, .ex_55a, .ex_60a, .ex_60b, .ex_63]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_1 => _root_.ChungMascarenhas2023.Examples.ex_1
  | .ex_15a => _root_.ChungMascarenhas2023.Examples.ex_15a
  | .ex_15b => _root_.ChungMascarenhas2023.Examples.ex_15b
  | .ex_15c => _root_.ChungMascarenhas2023.Examples.ex_15c
  | .ex_25a => _root_.ChungMascarenhas2023.Examples.ex_25a
  | .ex_25a_have_to => _root_.ChungMascarenhas2023.Examples.ex_25a_have_to
  | .ex_25b => _root_.ChungMascarenhas2023.Examples.ex_25b
  | .ex_25b_have_to => _root_.ChungMascarenhas2023.Examples.ex_25b_have_to
  | .ex_25c => _root_.ChungMascarenhas2023.Examples.ex_25c
  | .ex_25c_have_to => _root_.ChungMascarenhas2023.Examples.ex_25c_have_to
  | .ex_26a => _root_.ChungMascarenhas2023.Examples.ex_26a
  | .ex_26b => _root_.ChungMascarenhas2023.Examples.ex_26b
  | .ex_26b_have_to => _root_.ChungMascarenhas2023.Examples.ex_26b_have_to
  | .ex_26c => _root_.ChungMascarenhas2023.Examples.ex_26c
  | .ex_29a => _root_.ChungMascarenhas2023.Examples.ex_29a
  | .ex_29b => _root_.ChungMascarenhas2023.Examples.ex_29b
  | .ex_36 => _root_.ChungMascarenhas2023.Examples.ex_36
  | .ex_49a => _root_.ChungMascarenhas2023.Examples.ex_49a
  | .ex_49b => _root_.ChungMascarenhas2023.Examples.ex_49b
  | .ex_54a => _root_.ChungMascarenhas2023.Examples.ex_54a
  | .ex_55a => _root_.ChungMascarenhas2023.Examples.ex_55a
  | .ex_60a => _root_.ChungMascarenhas2023.Examples.ex_60a
  | .ex_60b => _root_.ChungMascarenhas2023.Examples.ex_60b
  | .ex_63 => _root_.ChungMascarenhas2023.Examples.ex_63

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.ChungMascarenhas2023.Examples.all := rfl

/-- The value the example records under `prejacent`. -/
def Example.prejacent : Example → Option Prejacent
  | .ex_1 => none
  | .ex_15a => some .blockNeither
  | .ex_15b => some .blockA
  | .ex_15c => some .blockB
  | .ex_25a => some .blockNeither
  | .ex_25a_have_to => some .blockNeither
  | .ex_25b => some .blockA
  | .ex_25b_have_to => some .blockA
  | .ex_25c => some .blockB
  | .ex_25c_have_to => some .blockB
  | .ex_26a => none
  | .ex_26b => some .blockNeither
  | .ex_26b_have_to => some .blockNeither
  | .ex_26c => none
  | .ex_29a => none
  | .ex_29b => none
  | .ex_36 => none
  | .ex_49a => none
  | .ex_49b => none
  | .ex_54a => none
  | .ex_55a => none
  | .ex_60a => none
  | .ex_60b => none
  | .ex_63 => none

theorem Example.prejacent_datum :
    ∀ x : Example, _root_.ChungMascarenhas2023.Examples.prejacent x.datum = x.prejacent := by
  decide +kernel

/-- The value the example records under `antecedent`. -/
def Example.antecedent : Example → Option Antecedent
  | .ex_1 => none
  | .ex_15a => none
  | .ex_15b => some .minersInA
  | .ex_15c => some .minersInB
  | .ex_25a => none
  | .ex_25a_have_to => none
  | .ex_25b => some .minersInA
  | .ex_25b_have_to => some .minersInA
  | .ex_25c => some .minersInB
  | .ex_25c_have_to => some .minersInB
  | .ex_26a => none
  | .ex_26b => none
  | .ex_26b_have_to => none
  | .ex_26c => none
  | .ex_29a => none
  | .ex_29b => none
  | .ex_36 => none
  | .ex_49a => none
  | .ex_49b => none
  | .ex_54a => none
  | .ex_55a => none
  | .ex_60a => none
  | .ex_60b => none
  | .ex_63 => none

theorem Example.antecedent_datum :
    ∀ x : Example, _root_.ChungMascarenhas2023.Examples.antecedent x.datum = x.antecedent := by
  decide +kernel

/-- The value the example records under `focus`. -/
def Example.focus : Example → Option Focus
  | .ex_1 => none
  | .ex_15a => none
  | .ex_15b => none
  | .ex_15c => none
  | .ex_25a => none
  | .ex_25a_have_to => none
  | .ex_25b => none
  | .ex_25b_have_to => none
  | .ex_25c => none
  | .ex_25c_have_to => none
  | .ex_26a => none
  | .ex_26b => none
  | .ex_26b_have_to => none
  | .ex_26c => none
  | .ex_29a => none
  | .ex_29b => none
  | .ex_36 => none
  | .ex_49a => none
  | .ex_49b => none
  | .ex_54a => none
  | .ex_55a => none
  | .ex_60a => none
  | .ex_60b => some .pat
  | .ex_63 => none

theorem Example.focus_datum :
    ∀ x : Example, _root_.ChungMascarenhas2023.Examples.focus x.datum = x.focus := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_1 => []
  | .ex_15a => [(.modal, .ought)]
  | .ex_15b => [(.modal, .ought)]
  | .ex_15c => [(.modal, .ought)]
  | .ex_25a => [(.modal, .must)]
  | .ex_25a_have_to => []
  | .ex_25b => [(.modal, .must)]
  | .ex_25b_have_to => []
  | .ex_25c => [(.modal, .must)]
  | .ex_25c_have_to => []
  | .ex_26a => []
  | .ex_26b => [(.modal, .must)]
  | .ex_26b_have_to => []
  | .ex_26c => []
  | .ex_29a => []
  | .ex_29b => []
  | .ex_36 => []
  | .ex_49a => []
  | .ex_49b => []
  | .ex_54a => []
  | .ex_55a => []
  | .ex_60a => [(.modal, .must)]
  | .ex_60b => [(.modal, .must)]
  | .ex_63 => []

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.ChungMascarenhas2023.Examples.label? · = some l)).filterMap _root_.ChungMascarenhas2023.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end ChungMascarenhas2023.Examples
