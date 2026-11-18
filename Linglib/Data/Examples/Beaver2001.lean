module

public import Linglib.Data.Examples.Schema

/-!
# `Beaver2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Beaver2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beaver2001.Examples`.
-/

@[expose] public section

namespace Beaver2001.Examples

def e52 : Datum :=
  { id := "beaver2001_e52"
    source := ⟨"beaver-2001", "E52"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I go to London, my sister will pick me up at the airport."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "definite (my sister)"), ("embedding", "consequent of conditional")] }

def e154 : Datum :=
  { id := "beaver2001_e154"
    source := ⟨"beaver-2001", "E154"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "consequent of conditional")] }

def e155 : Datum :=
  { id := "beaver2001_e155"
    source := ⟨"beaver-2001", "E155"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is unlikely that if Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is greater than it would be on Earth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "conditional under unlikely")] }

def e156 : Datum :=
  { id := "beaver2001_e156"
    source := ⟨"beaver-2001", "E156"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X and is bothered by the fact that his weight is greater than it would be on Earth, he won't stay long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "the fact that + factive bothered by"), ("embedding", "second conjunct of conditional antecedent")] }

def e168 : Datum :=
  { id := "beaver2001_e168"
    source := ⟨"beaver-2001", "E168"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna realises that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "none"), ("translation", "∂bih AND cb_a_bih"), ("entails", "bih")] }

def e169 : Datum :=
  { id := "beaver2001_e169"
    source := ⟨"beaver-2001", "E169"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna does not realise that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "negation"), ("translation", "NOT (∂bih AND cb_a_bih)"), ("entails", "bih")] }

def e172 : Datum :=
  { id := "beaver2001_e172"
    source := ⟨"beaver-2001", "E172"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Anna realises that Bertha is hiding, then she will find her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "antecedent of conditional"), ("translation", "(∂bih AND cb_a_bih) IMPLIES awfb"), ("entails", "bih")] }

def e173 : Datum :=
  { id := "beaver2001_e173"
    source := ⟨"beaver-2001", "E173"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anna might realise that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "might"), ("translation", "MIGHT(∂bih AND cb_a_bih)"), ("entails", "bih")] }

def e174 : Datum :=
  { id := "beaver2001_e174"
    source := ⟨"beaver-2001", "E174"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bertha regrets that Anna realises that she is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive regret over factive realise"), ("embedding", "complement of a factive"), ("translation", "∂(∂bih AND cb_a_bih) AND NVB_B_(∂_bih&cb_a_bih)"), ("entails", "bih AND cb_a_bih")] }

def e175 : Datum :=
  { id := "beaver2001_e175"
    source := ⟨"beaver-2001", "E175"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bertha is not in the kitchen, then Anna realises that Bertha is in the attic."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "consequent of conditional"), ("translation", "(NOT bc) IMPLIES (∂ba AND cb_a_ba)"), ("doesNotEntail", "ba"), ("entails", "(NOT bc) IMPLIES ba")] }

def e176 : Datum :=
  { id := "beaver2001_e176"
    source := ⟨"beaver-2001", "E176"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bertha is hiding, then Anna realises that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "consequent of conditional"), ("translation", "bih IMPLIES (∂bih AND cb_a_bih)"), ("doesNotEntail", "bih")] }

def e177 : Datum :=
  { id := "beaver2001_e177"
    source := ⟨"beaver-2001", "E177"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Perhaps Bertha is hiding and Anna realises that Bertha is hiding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "factive realise"), ("embedding", "second conjunct under might"), ("translation", "MIGHT(bih AND ∂bih AND cb_a_bih)"), ("doesNotEntail", "bih")] }

def e206 : Datum :=
  { id := "beaver2001_e206"
    source := ⟨"beaver-2001", "E206"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible there is a happy farmer, but, then again, it is possible that there are no happy farmers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "might phi and might not phi")] }

def e207 : Datum :=
  { id := "beaver2001_e207"
    source := ⟨"beaver-2001", "E207"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No farmer is happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "plain assertion")] }

def all : List Datum := [e52, e154, e155, e156, e168, e169, e172, e173, e174, e175, e176, e177, e206, e207]

end Beaver2001.Examples
