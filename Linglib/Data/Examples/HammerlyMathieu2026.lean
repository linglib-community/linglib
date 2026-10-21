module

public import Linglib.Data.Examples.Schema

/-!
# `HammerlyMathieu2026` — typed example data

Auto-generated from `Linglib/Data/Examples/HammerlyMathieu2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HammerlyMathieu2026.Examples`.
-/

@[expose] public section

namespace HammerlyMathieu2026.Examples

def ex_1a : Datum :=
  { id := "hammerlymathieu2026_1a"
    source := ⟨"hammerly-mathieu-2026", "(1a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "nin-gikendam mindido-d mooz"
    glossedTokens := [("nin-gikendam", "1-know.AI"), ("mindido-d", "big-3"), ("mooz", "moose")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("lda", "none")] }

def ex_1b : Datum :=
  { id := "hammerlymathieu2026_1b"
    source := ⟨"hammerly-mathieu-2026", "(1b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "nin-gikenim-aa mindido-d mooz"
    glossedTokens := [("nin-gikenim-aa", "1-know.TA-3"), ("mindido-d", "big-3"), ("mooz", "moose")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("lda", "subject")] }

def ex_6a : Datum :=
  { id := "hammerlymathieu2026_6a"
    source := ⟨"hammerly-mathieu-2026", "(6a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waaband-aan Tom gii-pashkizw-aa-d adikw-an"
    glossedTokens := [("in-gii-waaband-aan", "1-PAST-see.TI-0"), ("Tom", "Tom.PROX"), ("gii-pashkizw-aa-d", "PAST-shoot-3-3"), ("adikw-an", "caribou-OBV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "none")] }

def ex_6b : Datum :=
  { id := "hammerlymathieu2026_6b"
    source := ⟨"hammerly-mathieu-2026", "(6b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-aa Tom gii-pashkizw-aa-d adikw-an"
    glossedTokens := [("in-gii-waabam-aa", "1-PAST-see.TA-3"), ("Tom", "Tom.PROX"), ("gii-pashkizw-aa-d", "PAST-shoot-3-3"), ("adikw-an", "caribou-OBV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ea")] }

def ex_7 : Datum :=
  { id := "hammerlymathieu2026_7"
    source := ⟨"hammerly-mathieu-2026", "(7)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gii'-ikido gii'-niimi-d Ziibiins dibikong"
    glossedTokens := [("gii'-ikido", "PAST-say.TA.3"), ("gii'-niimi-d", "PAST-dance.AI-3"), ("Ziibiins", "Ziibiins"), ("dibikong", "last.night")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("disjoint", .acceptable), ("coreferent", .ungrammatical)]
    paperFeatures := [] }

def ex_9a : Datum :=
  { id := "hammerlymathieu2026_9a"
    source := ⟨"hammerly-mathieu-2026", "(9a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-aa John gii-paashkizw-aa-d adikw-an"
    glossedTokens := [("in-gii-waabam-aa", "1-PAST-see.TA-3"), ("John", "John.PROX"), ("gii-paashkizw-aa-d", "PAST-shoot.TA-3-3"), ("adikw-an", "caribou-OBV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ea"), ("order", "PROX V OBV")] }

def ex_9b : Datum :=
  { id := "hammerlymathieu2026_9b"
    source := ⟨"hammerly-mathieu-2026", "(9b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "ingii-waabamaa gii-paashkizwaad John adikwan"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ea"), ("order", "V PROX OBV")] }

def ex_9c : Datum :=
  { id := "hammerlymathieu2026_9c"
    source := ⟨"hammerly-mathieu-2026", "(9c)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "ingii-waabamaa gii-paashkizwaad adikwan John"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ea"), ("order", "V OBV PROX")] }

def ex_9d : Datum :=
  { id := "hammerlymathieu2026_9d"
    source := ⟨"hammerly-mathieu-2026", "(9d)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "ingii-waabamaa adikwan gii-paashkizwaad John"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ea"), ("order", "OBV V PROX")] }

def ex_10a : Datum :=
  { id := "hammerlymathieu2026_10a"
    source := ⟨"hammerly-mathieu-2026", "(10a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-imaa-n John gii-paashkizw-aa-d adikw-an"
    glossedTokens := [("in-gii-waabam-imaa-n", "1-PAST-see.TA-3′-3′"), ("John", "John.PROX"), ("gii-paashkizw-aa-d", "PAST-shoot.TA-3-3"), ("adikw-an", "caribou-OBV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ia"), ("order", "PROX V OBV")] }

def ex_10b : Datum :=
  { id := "hammerlymathieu2026_10b"
    source := ⟨"hammerly-mathieu-2026", "(10b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "ingii-waabamimaan gii-paashkizwaad inini adikwan"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ia"), ("order", "V PROX OBV")] }

def ex_10c : Datum :=
  { id := "hammerlymathieu2026_10c"
    source := ⟨"hammerly-mathieu-2026", "(10c)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "ingii-waabamimaan gii-paashkizwaad adikwan John"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ia"), ("order", "V OBV PROX")] }

def ex_10d : Datum :=
  { id := "hammerlymathieu2026_10d"
    source := ⟨"hammerly-mathieu-2026", "(10d)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "ingii-waabamimaan adikwan gii-paashkizwaad John"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "obv"), ("lda", "ia"), ("order", "OBV V PROX")] }

def ex_11a : Datum :=
  { id := "hammerlymathieu2026_11a"
    source := ⟨"hammerly-mathieu-2026", "(11a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-aa ikwe gii-miigwechiwi'-igo-d John-an"
    glossedTokens := [("in-gii-waabam-aa", "1-PAST-see.TA-3"), ("ikwe", "woman.PROX"), ("gii-miigwechiwi'-igo-d", "PAST-thank.TA-INV-3"), ("John-an", "John-OBV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "obv"), ("ia", "prox"), ("lda", "ia")] }

def ex_11b : Datum :=
  { id := "hammerlymathieu2026_11b"
    source := ⟨"hammerly-mathieu-2026", "(11b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-imaa-n John-an gii-miigwechiwi'-igo-d ikwe"
    glossedTokens := [("in-gii-waabam-imaa-n", "1-PAST-see.TA-3′-3′"), ("John-an", "John-OBV"), ("gii-miigwechiwi'-igo-d", "PAST-thank.TA-INV-3"), ("ikwe", "woman.PROX")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "obv"), ("ia", "prox"), ("lda", "ea")] }

def ex_12a : Datum :=
  { id := "hammerlymathieu2026_12a"
    source := ⟨"hammerly-mathieu-2026", "(12a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-ig John gii-miigwechiwi'-i-yan"
    glossedTokens := [("gi-gii-waabam-ig", "2-PAST-see.TA-INV"), ("John", "John.PROX"), ("gii-miigwechiwi'-i-yan", "PAST-thank.TA-1-2")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("lda", "ea")] }

def ex_12b : Datum :=
  { id := "hammerlymathieu2026_12b"
    source := ⟨"hammerly-mathieu-2026", "(12b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-ig John gii-miigwechiwi'-i-yan"
    glossedTokens := [("in-gii-waabam-ig", "1-PAST-see.TA-INV"), ("John", "John.PROX"), ("gii-miigwechiwi'-i-yan", "PAST-thank.TA-1-2")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("lda", "ia")] }

def ex_13a : Datum :=
  { id := "hammerlymathieu2026_13a"
    source := ⟨"hammerly-mathieu-2026", "(13a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-ig John gii-miigwechiwi'-in-aan"
    glossedTokens := [("in-gii-waabam-ig", "1-PAST-see.TA-INV"), ("John", "John.PROX"), ("gii-miigwechiwi'-in-aan", "PAST-thank.TA-2-1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("lda", "ea")] }

def ex_13b : Datum :=
  { id := "hammerlymathieu2026_13b"
    source := ⟨"hammerly-mathieu-2026", "(13b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-ig John gii-miigwechiwi'-in-aan"
    glossedTokens := [("gi-gii-waabam-ig", "2-PAST-see.TA-INV"), ("John", "John.PROX"), ("gii-miigwechiwi'-in-aan", "PAST-thank.TA-2-1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("lda", "ia")] }

def ex_14a : Datum :=
  { id := "hammerlymathieu2026_14a"
    source := ⟨"hammerly-mathieu-2026", "(14a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-in gii-miigwechiwi'-ad John"
    glossedTokens := [("gi-gii-waabam-in", "2-PAST-see.TA-2"), ("gii-miigwechiwi'-ad", "PAST-thank.TA-2>3"), ("John", "John.PROX")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "prox"), ("lda", "ea")] }

def ex_14b : Datum :=
  { id := "hammerlymathieu2026_14b"
    source := ⟨"hammerly-mathieu-2026", "(14b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-aa gii-miigwechiwi'-ad John"
    glossedTokens := [("in-gii-waabam-aa", "1-PAST-see.TA-3"), ("gii-miigwechiwi'-ad", "PAST-thank.TA-2>3"), ("John", "John.PROX")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "prox"), ("lda", "ia")] }

def ex_15a : Datum :=
  { id := "hammerlymathieu2026_15a"
    source := ⟨"hammerly-mathieu-2026", "(15a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "in-gii-waabam-aa ikwe gii-miiwechiwi'-ik"
    glossedTokens := [("in-gii-waabam-aa", "1-PAST-see.TA-3"), ("ikwe", "woman.PROX"), ("gii-miiwechiwi'-ik", "PAST-thank.TA-3>2")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "2"), ("lda", "ea")] }

def ex_15b : Datum :=
  { id := "hammerlymathieu2026_15b"
    source := ⟨"hammerly-mathieu-2026", "(15b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-in gii-miiwechiwi'-ik ikwe"
    glossedTokens := [("gi-gii-waabam-in", "2-PAST-see.TA-2"), ("gii-miiwechiwi'-ik", "PAST-thank.TA-3>2"), ("ikwe", "woman.PROX")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "2"), ("lda", "ia")] }

def ex_16a : Datum :=
  { id := "hammerlymathieu2026_16a"
    source := ⟨"hammerly-mathieu-2026", "(16a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-aa ina gii-miiwechiwi'-ag ikwe"
    glossedTokens := [("gi-gii-waabam-aa", "2-PAST-see.TA-3"), ("ina", "Q"), ("gii-miiwechiwi'(-aa)-ag", "PAST-thank.TA(-3)-1>3"), ("ikwe", "woman.PROX")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "prox"), ("lda", "ia")] }

def ex_16b : Datum :=
  { id := "hammerlymathieu2026_16b"
    source := ⟨"hammerly-mathieu-2026", "(16b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-aa ina ikwe gii-miiwechiwi'-ag"
    glossedTokens := [("gi-gii-waabam-aa", "2-PAST-see.TA-3"), ("ina", "Q"), ("ikwe", "woman.PROX"), ("gii-miiwechiwi'(-aa)-ag", "PAST-thank.TA(-3)-1>3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "prox"), ("lda", "ia")] }

def ex_17 : Datum :=
  { id := "hammerlymathieu2026_17"
    source := ⟨"hammerly-mathieu-2026", "(17)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam ina gii-miiwechiwi'-ag ikwe"
    glossedTokens := [("gi-gii-waabam(-i)", "2-PAST-see.TA(-1)"), ("ina", "Q"), ("gii-miiwechiwi'(-aa)-ag", "PAST-thank.TA(-3)-1>3"), ("ikwe", "woman.PROX")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "prox"), ("lda", "ea")] }

def ex_18a : Datum :=
  { id := "hammerlymathieu2026_18a"
    source := ⟨"hammerly-mathieu-2026", "(18a)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam-aa ina ikwe gii-miiwechiwi'-i-d"
    glossedTokens := [("gi-gii-waabam-aa", "2-PAST-see.TA-3"), ("ina", "Q"), ("ikwe", "woman.PROX"), ("gii-miiwechiwi'-i-d", "PAST-thank.TA-1-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "1"), ("lda", "ea")] }

def ex_18b : Datum :=
  { id := "hammerlymathieu2026_18b"
    source := ⟨"hammerly-mathieu-2026", "(18b)"⟩
    reportedIn := none
    language := "rain1239"
    primaryText := "gi-gii-waabam ina gii-miiwechiwi'-i-d ikwe"
    glossedTokens := [("gi-gii-waabam(-i)", "2-PAST-see.TA(-1)"), ("ina", "Q"), ("gii-miiwechiwi'-i-d", "PAST-thank.TA-1-3"), ("ikwe", "woman.PROX")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "prox"), ("ia", "1"), ("lda", "ia")] }

def all : List Datum := [ex_1a, ex_1b, ex_6a, ex_6b, ex_7, ex_9a, ex_9b, ex_9c, ex_9d, ex_10a, ex_10b, ex_10c, ex_10d, ex_11a, ex_11b, ex_12a, ex_12b, ex_13a, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17, ex_18a, ex_18b]

end HammerlyMathieu2026.Examples
