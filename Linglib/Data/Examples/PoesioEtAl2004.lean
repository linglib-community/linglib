module

public import Linglib.Data.Examples.Schema

/-!
# `PoesioEtAl2004` — typed example data

Auto-generated from `Linglib/Data/Examples/PoesioEtAl2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace PoesioEtAl2004.Examples`.
-/

@[expose] public section

namespace PoesioEtAl2004.Examples

def ex5 : Datum :=
  { id := "poesioetal2004_ex5"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John walked toward the house. The door was open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("parameter", "realization"), ("section", "2.4.2")] }

def ex7 : Datum :=
  { id := "poesioetal2004_ex7"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should not use PRODUCT-Z if you are pregnant or breast-feeding. Whilst you are receiving PRODUCT-Z ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("parameter", "cfFilter"), ("parameter", "previousUtterance"), ("section", "2.4.2")] }

def ex9 : Datum :=
  { id := "poesioetal2004_ex9"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These \"egg vases\" are of exceptional quality: basketwork bases support egg-shaped bodies and bundles of straw form the handles, while small eggs resting in straw nests serve as the finial for each lid. Each vase is decorated with inlaid decoration: ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("parameter", "utterance"), ("parameter", "realization"), ("section", "4.1.1")] }

def ex10 : Datum :=
  { id := "poesioetal2004_ex10"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The drawing of the corner cupboard, or more probably an engraving of it, must have caught Branicki's attention. Dubois was commissioned through a Warsaw dealer to construct the cabinet for the Polish aristocrat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("parameter", "rank"), ("section", "4.1.1")] }

def ex14 : Datum :=
  { id := "poesioetal2004_ex14"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John woke up when Bill rang the door. He had forgotten the appointment."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("parameter", "previousUtterance"), ("section", "4.2.5")] }

def ex16 : Datum :=
  { id := "poesioetal2004_ex16"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do not use scissors as you may damage the patch inside. Take out the patch."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("parameter", "previousUtterance"), ("section", "4.2.5")] }

def ex23 : Datum :=
  { id := "poesioetal2004_ex23"
    source := ⟨"poesio-stevenson-eugenio-hitzeman-2004", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This leaflet is a summary of the important information about Product A. If you have any questions or are not sure about anything to do with your treatment, ask your doctor or your pharmacist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2.2")] }

def all : List Datum := [ex5, ex7, ex9, ex10, ex14, ex16, ex23]

end PoesioEtAl2004.Examples
