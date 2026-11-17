module

public import Linglib.Data.Examples.Schema

/-!
# `BadeEtAl2022` — typed example data

Auto-generated from `Linglib/Data/Examples/BadeEtAl2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BadeEtAl2022.Examples`.
-/

@[expose] public section

namespace BadeEtAl2022.Examples

def bpcm2022_1_disjunction : Datum :=
  { id := "bpcm2022_1_disjunction"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary speaks French."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow from the two premises? Simplified from Walsh & Johnson-Laird's original items."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "disjunction"), ("structure", "canonical"), ("acceptance", "80-85%")] }

def bpcm2022_3_indefinite : Datum :=
  { id := "bpcm2022_3_indefinite"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John writes poems."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow from the two premises?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "indefinite"), ("structure", "canonical"), ("acceptance", "35% (Mascarenhas & Koralus 2017)")] }

def bpcm2022_6_might_london : Datum :=
  { id := "bpcm2022_6_might_london"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John might be in London."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("form", "John is in London ∨ ⊤ (7a)"), ("alternatives", "{John is in London, ⊤} (7b)"), ("analysis", "attentive content, Ciardelli, Groenendijk & Roelofsen 2009")] }

def bpcm2022_10_miranda : Datum :=
  { id := "bpcm2022_10_miranda"
    source := ⟨"mascarenhas-picat-2019", "(7)"⟩
    reportedIn := some ⟨"bade-picat-chung-mascarenhas-2022", "(10)"⟩
    language := "stan1293"
    primaryText := "Miranda is afraid of spiders."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow from the two premises?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "might"), ("structure", "canonical")] }

def bpcm2022_13a_epistemic : Datum :=
  { id := "bpcm2022_13a_epistemic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave to the poor."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow from the two premises?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "might"), ("structure", "canonical"), ("modal", "epistemic")] }

def bpcm2022_13a_deontic : Datum :=
  { id := "bpcm2022_13a_deontic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave to the poor."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow from the two premises?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "allowed to"), ("structure", "canonical"), ("modal", "deontic")] }

def bpcm2022_13b_epistemic : Datum :=
  { id := "bpcm2022_13b_epistemic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave to the poor."
    glossedTokens := []
    context := "Reasoning task, flat structure: both premises combined into one sentence."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "might"), ("structure", "flat"), ("modal", "epistemic")] }

def bpcm2022_13b_deontic : Datum :=
  { id := "bpcm2022_13b_deontic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave to the poor."
    glossedTokens := []
    context := "Reasoning task, flat structure: both premises combined into one sentence."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "allowed to"), ("structure", "flat"), ("modal", "deontic")] }

def bpcm2022_13c_epistemic : Datum :=
  { id := "bpcm2022_13c_epistemic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave to the poor."
    glossedTokens := []
    context := "Reasoning task, reversed structure: the hint precedes the alternative-raising premise."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "might"), ("structure", "reversed"), ("modal", "epistemic")] }

def bpcm2022_13c_deontic : Datum :=
  { id := "bpcm2022_13c_deontic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(13c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave to the poor."
    glossedTokens := []
    context := "Reasoning task, reversed structure: the hint precedes the alternative-raising premise."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("generator", "allowed to"), ("structure", "reversed"), ("modal", "deontic")] }

def bpcm2022_16_package_deal : Datum :=
  { id := "bpcm2022_16_package_deal"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is allowed to steal from the rich and give to the poor."
    glossedTokens := []
    context := "Package deal (Merin 1992, van Rooy 2000): permission for both actions or neither."
    judgment := .acceptable
    contrasts := []
    readings := [("John is allowed to steal from the rich (16a)", .unacceptable)]
    paperFeatures := [("inference", "package deal"), ("reading", "biconditional permission (van Rooy 2000)")] }

def bpcm2022_app_daniel_deontic : Datum :=
  { id := "bpcm2022_app_daniel_deontic"
    source := ⟨"bade-picat-chung-mascarenhas-2022", "Appendix, Targets"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Daniel went to a march in Washington."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow from the two premises?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("itemType", "target"), ("generator", "allowed to"), ("modal", "deontic")] }

def all : List Datum := [bpcm2022_1_disjunction, bpcm2022_3_indefinite, bpcm2022_6_might_london, bpcm2022_10_miranda, bpcm2022_13a_epistemic, bpcm2022_13a_deontic, bpcm2022_13b_epistemic, bpcm2022_13b_deontic, bpcm2022_13c_epistemic, bpcm2022_13c_deontic, bpcm2022_16_package_deal, bpcm2022_app_daniel_deontic]

end BadeEtAl2022.Examples
