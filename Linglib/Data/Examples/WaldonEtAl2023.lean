module

public import Linglib.Data.Examples.Schema

/-!
# `WaldonEtAl2023` — typed example data

Auto-generated from `Linglib/Data/Examples/WaldonEtAl2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WaldonEtAl2023.Examples`.
-/

@[expose] public section

namespace WaldonEtAl2023.Examples

def ex_1 : Datum :=
  { id := "waldonetal2023_1"
    source := ⟨"hart-1958", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(1)"⟩
    language := "stan1293"
    primaryText := "A legal rule forbids you to take a vehicle into the public park."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Hart's vehicle rule")] }

def rule : Datum :=
  { id := "waldonetal2023_rule"
    source := ⟨"waldon-etal-2023", "§3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No electronic devices are allowed in the theater."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("rule", "prohibition"), ("artifactNoun", "electronic device")] }

def ex_4a : Datum :=
  { id := "waldonetal2023_4a"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(4a)"⟩
    language := "stan1293"
    primaryText := "This tree is a pine in some respects."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("This tree is a pine in most respects.", .unacceptable), ("This tree is a pine in every respect.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "dimensional"), ("nounType", "natural kind")] }

def ex_4b : Datum :=
  { id := "waldonetal2023_4b"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(4b)"⟩
    language := "stan1293"
    primaryText := "This place is a church in some respects."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("construction", "dimensional"), ("nounType", "artifact")] }

def ex_4c : Datum :=
  { id := "waldonetal2023_4c"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(4c)"⟩
    language := "stan1293"
    primaryText := "This place is safe in some respects."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "dimensional"), ("nounType", "multidimensional adjective")] }

def ex_5a : Datum :=
  { id := "waldonetal2023_5a"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(5a)"⟩
    language := "stan1293"
    primaryText := "This tree is more a pine than that one."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("This tree is more a pine than an oak.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "natural kind")] }

def ex_5b : Datum :=
  { id := "waldonetal2023_5b"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(5b)"⟩
    language := "stan1293"
    primaryText := "This place is more a church than that one."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := [("This place is more a church than an art gallery.", .marginal)]
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "artifact")] }

def ex_5c : Datum :=
  { id := "waldonetal2023_5c"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(5c)"⟩
    language := "stan1293"
    primaryText := "This place is more safe than that one."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "multidimensional adjective")] }

def ex_7 : Datum :=
  { id := "waldonetal2023_7"
    source := ⟨"waldon-etal-2023", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This tree is taller than that one."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("This tree is taller than it is wide.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "single-dimensional adjective")] }

def ex_10a : Datum :=
  { id := "waldonetal2023_10a"
    source := ⟨"waldon-etal-2023", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every vehicle is prohibited from the park."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "quantificational"), ("parameters", "F, W, s")] }

def ex_11a : Datum :=
  { id := "waldonetal2023_11a"
    source := ⟨"waldon-etal-2023", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This object is more (of) a vehicle than that one."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("construction", "degree"), ("parameters", "F, W project")] }

def ex_16a : Datum :=
  { id := "waldonetal2023_16a"
    source := ⟨"waldon-etal-2023", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No electronic devices are allowed in the theater. By the way: for our purposes, a flashlight counts as an electronic device."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "meta-linguistic negotiation")] }

def ex_16b : Datum :=
  { id := "waldonetal2023_16b"
    source := ⟨"waldon-etal-2023", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Get me a long ladder. By the way: for our purposes, 20 feet counts as long for a ladder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "meta-linguistic negotiation")] }

def ex_16c : Datum :=
  { id := "waldonetal2023_16c"
    source := ⟨"waldon-etal-2023", "(16c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put all the bottles of Heineken in the fridge. By the way: for our purposes, nothing that my neighbors bought for their party counts as a bottle of Heineken."
    glossedTokens := []
    context := "Planning a party."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("test", "meta-linguistic negotiation"), ("analysis", "domain restriction")] }

def all : List Datum := [ex_1, rule, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_5c, ex_7, ex_10a, ex_11a, ex_16a, ex_16b, ex_16c]

end WaldonEtAl2023.Examples
