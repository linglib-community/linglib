module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintelIatridou2005` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintelIatridou2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintelIatridou2005.Examples`.
-/

@[expose] public section

namespace VonFintelIatridou2005.Examples

def vFI2005_1_harlem : Datum :=
  { id := "vFI2005_1_harlem"
    source := ⟨"von-fintel-iatridou-2005", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you have to take the A train."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase")] }

def vFI2005_2_sugarWaiter : Datum :=
  { id := "vFI2005_2_sugarWaiter"
    source := ⟨"hare-1971", "p. 45"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "(2)"⟩
    language := "stan1293"
    primaryText := "If you want sugar in your soup, you should ask the waiter."
    glossedTokens := []
    context := "Waiter has the only access to sugar."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "hareMinimalPair"), ("reading", "anankastic")] }

def vFI2005_3_sugarDiabetes : Datum :=
  { id := "vFI2005_3_sugarDiabetes"
    source := ⟨"hare-1971", "p. 45"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "(3)"⟩
    language := "stan1293"
    primaryText := "If you want sugar in your soup, you should get tested for diabetes."
    glossedTokens := []
    context := "Excessive desire for sugar may indicate diabetes."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "hareMinimalPair"), ("reading", "non-anankastic")] }

def vFI2005_4_harlemPurpose : Datum :=
  { id := "vFI2005_4_harlemPurpose"
    source := ⟨"von-fintel-iatridou-2005", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To go to Harlem, you have to take the A train."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("clauseType", "purpose")] }

def vFI2005_11_hoboken : Datum :=
  { id := "vFI2005_11_hoboken"
    source := ⟨"von-fintel-iatridou-2005", "(1), §3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you have to take the A train."
    glossedTokens := []
    context := "You actually want to go to Hoboken; I do not know that. Best way to Hoboken is the PATH train; best way to Harlem is the A train."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "hoboken")] }

def vFI2005_13_hobokenSaebo : Datum :=
  { id := "vFI2005_13_hobokenSaebo"
    source := ⟨"von-fintel-iatridou-2005", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you should take the A train."
    glossedTokens := []
    context := "In the actual world you want to go to Hoboken; I do not know that and am uncertain whether you want to go to Hoboken or to Harlem. The best way to Hoboken is the PATH train, the best way to Harlem is the A train; there is not enough time to go to both places."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "conflictingGoals")] }

def vFI2005_22_mayorPub : Datum :=
  { id := "vFI2005_22_mayorPub"
    source := ⟨"kratzer-1991", "mayor scenario"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "(22)"⟩
    language := "stan1293"
    primaryText := "If you want to become mayor, you have to go to the pub regularly."
    glossedTokens := []
    context := "You want to become mayor. You also want to not go to the pub regularly. You will become mayor only if you go to the pub regularly."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "conflictingGoals")] }

def vFI2005_p12_vanNistelrooy : Datum :=
  { id := "vFI2005_p12_vanNistelrooy"
    source := ⟨"von-fintel-iatridou-2005", "(1), §5 (scenario by Huitink)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you have to take the A train."
    glossedTokens := []
    context := "Either A train or C train goes to Harlem. You are an incorrigible fan of Ruud van Nistelrooy and most want to meet him. Van Nistelrooy regularly rides the A train."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "correlatedIrrelevant"), ("holds", "no")] }

def vFI2005_36_pedroMartinez : Datum :=
  { id := "vFI2005_36_pedroMartinez"
    source := ⟨"nissenbaum-2005", "Pedro Martinez"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "(36)"⟩
    language := "stan1293"
    primaryText := "To go to Harlem, you ought to kiss Pedro Martinez."
    glossedTokens := []
    context := "Both the A train and the C train go to Harlem. The C train will have Pedro Martinez on it. You want to kiss Pedro Martinez."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "nonCausalCoincidence")] }

def vFI2005_34c_harlemBreathe : Datum :=
  { id := "vFI2005_34c_harlemBreathe"
    source := ⟨"vonstechow-krasikova-penka-2005", "breathe example"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "(34d)"⟩
    language := "stan1293"
    primaryText := "In order to go to Harlem, you have to breathe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "triviallyTrue"), ("modal", "have-to")] }

def vFI2005_35_harlemBreatheOught : Datum :=
  { id := "vFI2005_35_harlemBreatheOught"
    source := ⟨"von-fintel-iatridou-2005", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To go to Harlem, you ought to breathe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "triviallyTrue"), ("modal", "ought-to"), ("felicity", "infelicitous")] }

def vFI2005_23_slomanOughtNot : Datum :=
  { id := "vFI2005_23_slomanOughtNot"
    source := ⟨"von-fintel-iatridou-2005", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You ought to take the train, but you don't have to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "oughtVsHaveTo")] }

def vFI2005_p13_londonByNoon : Datum :=
  { id := "vFI2005_p13_londonByNoon"
    source := ⟨"sloman-1970", "p. 391"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "§6.1"⟩
    language := "stan1293"
    primaryText := "If you want to get to London by noon, then you ought to go by train."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("If you want to get to London by noon then you have to go by train.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "oughtVsHaveTo")] }

def vFI2005_29_vladivostokHave : Datum :=
  { id := "vFI2005_29_vladivostokHave"
    source := ⟨"vonstechow-krasikova-penka-2005", "Vladivostok"⟩
    reportedIn := some ⟨"von-fintel-iatridou-2005", "(29)"⟩
    language := "stan1293"
    primaryText := "To go to Vladivostok, you have to take the Chinese train."
    glossedTokens := []
    context := "Two trains cross Siberia to Vladivostok: Russian and Chinese. The Chinese train is significantly more comfortable."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "vladivostokOughtHave"), ("modal", "have-to"), ("speakerVariation", "Klein-vs-Percus")] }

def vFI2005_30_vladivostokOught : Datum :=
  { id := "vFI2005_30_vladivostokOught"
    source := ⟨"von-fintel-iatridou-2005", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To go to Vladivostok, you ought to take the Chinese train."
    glossedTokens := []
    context := "Same Vladivostok scenario."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "vladivostokOughtHave"), ("modal", "ought-to")] }

def vFI2005_28_burdicks : Datum :=
  { id := "vFI2005_28_burdicks"
    source := ⟨"von-fintel-iatridou-2005", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I'm going to Harvard Square tomorrow. B: You have to have some hot chocolate at Burdick's."
    glossedTokens := []
    context := "A announces an itinerary; no to-clause or if-clause overtly supplies a goal."
    judgment := .acceptable
    contrasts := [("You ought to have some hot chocolate at Burdick's.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "contextualDesignation")] }

def vFI2005_20_weinerJoe : Datum :=
  { id := "vFI2005_20_weinerJoe"
    source := ⟨"von-fintel-iatridou-2005", "(20) (scenario by Weiner)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Joe wants to go to Harlem, he must take the A train."
    glossedTokens := []
    context := "Joe has been considering buying a used car in Harlem. If he hasn't bought it yet, the A train is his only way to Harlem; if he has bought it, he can drive or take the A train. The only reason Joe would want Harlem is to buy the car (so if he wants Harlem, he hasn't bought it)."
    judgment := .acceptable
    contrasts := []
    readings := [("epistemic", .marginal), ("anankastic", .acceptable)]
    paperFeatures := [("puzzle", "weinerJoe")] }

def all : List Datum := [vFI2005_1_harlem, vFI2005_2_sugarWaiter, vFI2005_3_sugarDiabetes, vFI2005_4_harlemPurpose, vFI2005_11_hoboken, vFI2005_13_hobokenSaebo, vFI2005_22_mayorPub, vFI2005_p12_vanNistelrooy, vFI2005_36_pedroMartinez, vFI2005_34c_harlemBreathe, vFI2005_35_harlemBreatheOught, vFI2005_23_slomanOughtNot, vFI2005_p13_londonByNoon, vFI2005_29_vladivostokHave, vFI2005_30_vladivostokOught, vFI2005_28_burdicks, vFI2005_20_weinerJoe]

end VonFintelIatridou2005.Examples
