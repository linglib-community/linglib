module

public import Linglib.Data.Examples.Schema

/-!
# `Carlson1977` — typed example data

Auto-generated from `Linglib/Data/Examples/Carlson1977.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Carlson1977.Examples`.
-/

@[expose] public section

namespace Carlson1977.Examples

def ex_119 : Datum :=
  { id := "carlson1977_119"
    source := ⟨"carlson-1977", "(119)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are sitting on my lawn. All dogs are mammals. Therefore: Mammals are sitting on my lawn."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_120 : Datum :=
  { id := "carlson1977_120"
    source := ⟨"carlson-1977", "(120)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are good pets. All dogs are mammals. Therefore: Mammals are good pets."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_131 : Datum :=
  { id := "carlson1977_131"
    source := ⟨"carlson-1977", "(131)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max believes some dogs are here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("transparent", .acceptable), ("opaque", .acceptable)]
    paperFeatures := [] }

def ex_132 : Datum :=
  { id := "carlson1977_132"
    source := ⟨"carlson-1977", "(132)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max believes dogs are here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("transparent", .unacceptable), ("opaque", .acceptable)]
    paperFeatures := [] }

def ex_135a : Datum :=
  { id := "carlson1977_135a"
    source := ⟨"carlson-1977", "(135a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jake is everywhere."
    glossedTokens := []
    context := "Read literally, of a world like ours, in which a particular individual can be in only one place at a time, and with dogs at every relevant place."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_135b : Datum :=
  { id := "carlson1977_135b"
    source := ⟨"carlson-1977", "(135b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some dog is everywhere."
    glossedTokens := []
    context := "Read literally, of a world like ours, in which a particular individual can be in only one place at a time, and with dogs at every relevant place."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_135c : Datum :=
  { id := "carlson1977_135c"
    source := ⟨"carlson-1977", "(135c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are everywhere."
    glossedTokens := []
    context := "Read literally, of a world like ours, in which a particular individual can be in only one place at a time, and with dogs at every relevant place."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_119, ex_120, ex_131, ex_132, ex_135a, ex_135b, ex_135c]

end Carlson1977.Examples
