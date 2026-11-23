module

public import Linglib.Data.Examples.Schema

/-!
# `Heim2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim2006.Examples`.
-/

@[expose] public section

namespace Heim2006.Examples

def ex_1 : Datum :=
  { id := "heim2006_1"
    source := ⟨"heim-2006", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucinda is driving less fast than is allowed on this highway."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("her speed is below the maximum speed allowed", .acceptable), ("her speed is below the minimum speed allowed", .acceptable)]
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "heim2006_2a"
    source := ⟨"heim-2006", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We can grow very little."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("growing very little is a possibility", .acceptable), ("growing very little is a necessity", .acceptable)]
    paperFeatures := [] }

def ex_2b : Datum :=
  { id := "heim2006_2b"
    source := ⟨"heim-2006", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't realize how little I can pay."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("I thought I would have to pay more", .acceptable), ("I thought I would be able to pay more", .acceptable)]
    paperFeatures := [] }

def ex_2c : Datum :=
  { id := "heim2006_2c"
    source := ⟨"heim-2006", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's a shame that they let the students write so little!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("they should have been required to write more", .acceptable), ("they should be allowed to write more", .acceptable)]
    paperFeatures := [] }

def ex_32 : Datum :=
  { id := "heim2006_32"
    source := ⟨"heim-2006", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucinda is driving faster than is allowed on this highway."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("her speed is above the maximum speed allowed", .acceptable), ("her speed is above the minimum speed allowed", .unacceptable)]
    paperFeatures := [] }

def ex_34a : Datum :=
  { id := "heim2006_34a"
    source := ⟨"heim-2006", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We can grow very much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("growing very much is a possibility", .acceptable), ("growing very much is a necessity", .unacceptable)]
    paperFeatures := [] }

def ex_35c : Datum :=
  { id := "heim2006_35c"
    source := ⟨"heim-2006", "(35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paul ate less than was necessary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he ate less than the diet would have allowed", .acceptable), ("he did not eat enough to maintain his weight", .acceptable)]
    paperFeatures := [] }

def ex_44 : Datum :=
  { id := "heim2006_44"
    source := ⟨"heim-2006", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucinda is driving more slowly than is allowed on this highway."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("her speed is below the maximum speed allowed", .acceptable), ("her speed is below the minimum speed allowed", .acceptable)]
    paperFeatures := [] }

def ex_46a : Datum :=
  { id := "heim2006_46a"
    source := ⟨"heim-2006", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary needs to drive faster than John needs to drive."
    glossedTokens := []
    context := "John and Mary must both be in Boston by 8pm; at 5:30pm John sets out from Providence and Mary from New Haven, which is farther."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_46b : Datum :=
  { id := "heim2006_46b"
    source := ⟨"heim-2006", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs to drive less fast than Mary needs to drive."
    glossedTokens := []
    context := "John and Mary must both be in Boston by 8pm; at 5:30pm John sets out from Providence and Mary from New Haven, which is farther."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_46c : Datum :=
  { id := "heim2006_46c"
    source := ⟨"heim-2006", "(46c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs to drive more slowly than Mary needs to drive."
    glossedTokens := []
    context := "John and Mary must both be in Boston by 8pm; at 5:30pm John sets out from Providence and Mary from New Haven, which is farther."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1, ex_2a, ex_2b, ex_2c, ex_32, ex_34a, ex_35c, ex_44, ex_46a, ex_46b, ex_46c]

end Heim2006.Examples
