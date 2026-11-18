module

public import Linglib.Data.Examples.Schema

/-!
# `RoelofsenFarkas2015` — typed example data

Auto-generated from `Linglib/Data/Examples/RoelofsenFarkas2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RoelofsenFarkas2015.Examples`.
-/

@[expose] public section

namespace RoelofsenFarkas2015.Examples

def ex_6a_yes : Datum :=
  { id := "roelofsenfarkas2015_6a_yes"
    source := ⟨"roelofsen-farkas-2015", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter passed the test. Yes, he did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "yes")] }

def ex_6a_no : Datum :=
  { id := "roelofsenfarkas2015_6a_no"
    source := ⟨"roelofsen-farkas-2015", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter passed the test. No, he did."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "no")] }

def ex_6b_yes : Datum :=
  { id := "roelofsenfarkas2015_6b_yes"
    source := ⟨"roelofsen-farkas-2015", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter passed the test. Yes, he didn't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "yes")] }

def ex_6b_no : Datum :=
  { id := "roelofsenfarkas2015_6b_no"
    source := ⟨"roelofsen-farkas-2015", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter passed the test. No, he didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "no")] }

def ex_7a_yes : Datum :=
  { id := "roelofsenfarkas2015_7a_yes"
    source := ⟨"roelofsen-farkas-2015", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter didn't pass the test. Yes, he didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "yes")] }

def ex_7a_no : Datum :=
  { id := "roelofsenfarkas2015_7a_no"
    source := ⟨"roelofsen-farkas-2015", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter didn't pass the test. No, he didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "no")] }

def ex_7b_yes : Datum :=
  { id := "roelofsenfarkas2015_7b_yes"
    source := ⟨"roelofsen-farkas-2015", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter didn't pass the test. Yes, he DID."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "yes")] }

def ex_7b_no : Datum :=
  { id := "roelofsenfarkas2015_7b_no"
    source := ⟨"roelofsen-farkas-2015", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter didn't pass the test. No, he DID."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "no")] }

def ex_119_oui : Datum :=
  { id := "roelofsenfarkas2015_119_oui"
    source := ⟨"roelofsen-farkas-2015", "(119)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude est à la maison. B: Oui, elle y est."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "oui")] }

def ex_119_non : Datum :=
  { id := "roelofsenfarkas2015_119_non"
    source := ⟨"roelofsen-farkas-2015", "(119)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude est à la maison. B: Non, elle y est."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "non")] }

def ex_119_si : Datum :=
  { id := "roelofsenfarkas2015_119_si"
    source := ⟨"roelofsen-farkas-2015", "(119)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude est à la maison. B: Si, elle y est."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "si")] }

def ex_120_oui : Datum :=
  { id := "roelofsenfarkas2015_120_oui"
    source := ⟨"roelofsen-farkas-2015", "(120)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude n'est pas à la maison. B: Oui, elle n'y est pas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "oui")] }

def ex_120_non : Datum :=
  { id := "roelofsenfarkas2015_120_non"
    source := ⟨"roelofsen-farkas-2015", "(120)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude n'est pas à la maison. B: Non, elle n'y est pas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "non")] }

def ex_120_si : Datum :=
  { id := "roelofsenfarkas2015_120_si"
    source := ⟨"roelofsen-farkas-2015", "(120)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude n'est pas à la maison. B: Si, elle n'y est pas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "si")] }

def ex_121_oui : Datum :=
  { id := "roelofsenfarkas2015_121_oui"
    source := ⟨"roelofsen-farkas-2015", "(121)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude n'est pas à la maison. B: Oui, elle y est."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "oui")] }

def ex_121_non : Datum :=
  { id := "roelofsenfarkas2015_121_non"
    source := ⟨"roelofsen-farkas-2015", "(121)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude n'est pas à la maison. B: Non, elle y est."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "non")] }

def ex_121_si : Datum :=
  { id := "roelofsenfarkas2015_121_si"
    source := ⟨"roelofsen-farkas-2015", "(121)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude n'est pas à la maison. B: Si, elle y est."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "si")] }

def ex_122_oui : Datum :=
  { id := "roelofsenfarkas2015_122_oui"
    source := ⟨"roelofsen-farkas-2015", "(122)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude est à la maison. B: Oui, elle n'y est pas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "oui")] }

def ex_122_non : Datum :=
  { id := "roelofsenfarkas2015_122_non"
    source := ⟨"roelofsen-farkas-2015", "(122)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude est à la maison. B: Non, elle n'y est pas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "non")] }

def ex_122_si : Datum :=
  { id := "roelofsenfarkas2015_122_si"
    source := ⟨"roelofsen-farkas-2015", "(122)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A: Claude est à la maison. B: Si, elle n'y est pas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "si")] }

def ex_124_ja : Datum :=
  { id := "roelofsenfarkas2015_124_ja"
    source := ⟨"roelofsen-farkas-2015", "(124)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist zu Hause. B: Ja, sie ist zu Hause."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "ja")] }

def ex_124_nein : Datum :=
  { id := "roelofsenfarkas2015_124_nein"
    source := ⟨"roelofsen-farkas-2015", "(124)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist zu Hause. B: Nein, sie ist zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "nein")] }

def ex_124_doch : Datum :=
  { id := "roelofsenfarkas2015_124_doch"
    source := ⟨"roelofsen-farkas-2015", "(124)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist zu Hause. B: Doch, sie ist zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "positive"), ("relative", "agree"), ("particle", "doch")] }

def ex_125_ja : Datum :=
  { id := "roelofsenfarkas2015_125_ja"
    source := ⟨"roelofsen-farkas-2015", "(125)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist nicht zu Hause. B: Ja, sie ist nicht zu Hause."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "ja")] }

def ex_125_nein : Datum :=
  { id := "roelofsenfarkas2015_125_nein"
    source := ⟨"roelofsen-farkas-2015", "(125)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist nicht zu Hause. B: Nein, sie ist nicht zu Hause."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "nein")] }

def ex_125_doch : Datum :=
  { id := "roelofsenfarkas2015_125_doch"
    source := ⟨"roelofsen-farkas-2015", "(125)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist nicht zu Hause. B: Doch, sie ist nicht zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "negative"), ("relative", "agree"), ("particle", "doch")] }

def ex_126_ja : Datum :=
  { id := "roelofsenfarkas2015_126_ja"
    source := ⟨"roelofsen-farkas-2015", "(126)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist nicht zu Hause. B: Ja, sie ist zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "ja")] }

def ex_126_nein : Datum :=
  { id := "roelofsenfarkas2015_126_nein"
    source := ⟨"roelofsen-farkas-2015", "(126)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist nicht zu Hause. B: Nein, sie ist zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "nein")] }

def ex_126_doch : Datum :=
  { id := "roelofsenfarkas2015_126_doch"
    source := ⟨"roelofsen-farkas-2015", "(126)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist nicht zu Hause. B: Doch, sie ist zu Hause."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "negative"), ("response", "positive"), ("relative", "reverse"), ("particle", "doch")] }

def ex_127_ja : Datum :=
  { id := "roelofsenfarkas2015_127_ja"
    source := ⟨"roelofsen-farkas-2015", "(127)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist zu Hause. B: Ja, sie ist nicht zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "ja")] }

def ex_127_nein : Datum :=
  { id := "roelofsenfarkas2015_127_nein"
    source := ⟨"roelofsen-farkas-2015", "(127)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist zu Hause. B: Nein, sie ist nicht zu Hause."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "nein")] }

def ex_127_doch : Datum :=
  { id := "roelofsenfarkas2015_127_doch"
    source := ⟨"roelofsen-farkas-2015", "(127)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "A: Katharina ist zu Hause. B: Doch, sie ist nicht zu Hause."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("antecedent", "positive"), ("response", "negative"), ("relative", "reverse"), ("particle", "doch")] }

def ex_49_yes : Datum :=
  { id := "roelofsenfarkas2015_49_yes"
    source := ⟨"roelofsen-farkas-2015", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets even? B: Yes, it is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("radical", "even"), ("antecedent", "positive"), ("response", "positive"), ("particle", "yes"), ("conveys", "even")] }

def ex_49_no : Datum :=
  { id := "roelofsenfarkas2015_49_no"
    source := ⟨"roelofsen-farkas-2015", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets even? B: No, it isn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("radical", "even"), ("antecedent", "positive"), ("response", "negative"), ("particle", "no"), ("conveys", "odd")] }

def ex_50_yes : Datum :=
  { id := "roelofsenfarkas2015_50_yes"
    source := ⟨"roelofsen-farkas-2015", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets odd? B: Yes, it is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("radical", "odd"), ("antecedent", "positive"), ("response", "positive"), ("particle", "yes"), ("conveys", "odd")] }

def ex_50_no : Datum :=
  { id := "roelofsenfarkas2015_50_no"
    source := ⟨"roelofsen-farkas-2015", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets odd? B: No, it isn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("radical", "odd"), ("antecedent", "positive"), ("response", "negative"), ("particle", "no"), ("conveys", "even")] }

def ex_51_yes : Datum :=
  { id := "roelofsenfarkas2015_51_yes"
    source := ⟨"roelofsen-farkas-2015", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets even↑, or odd↓? B: Yes, it is."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "alternativeQuestion"), ("response", "positive"), ("particle", "yes")] }

def ex_51_no : Datum :=
  { id := "roelofsenfarkas2015_51_no"
    source := ⟨"roelofsen-farkas-2015", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets even↑, or odd↓? B: No, it isn't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "alternativeQuestion"), ("response", "negative"), ("particle", "no")] }

def ex_52_no : Datum :=
  { id := "roelofsenfarkas2015_52_no"
    source := ⟨"roelofsen-farkas-2015", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets odd↑? B: No, it isn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("radical", "odd"), ("antecedent", "positive"), ("response", "negative"), ("particle", "no"), ("conveys", "not odd")] }

def ex_53_no : Datum :=
  { id := "roelofsenfarkas2015_53_no"
    source := ⟨"roelofsen-farkas-2015", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is the number of planets not even↑? B: No, it isn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("radical", "even"), ("antecedent", "negative"), ("response", "negative"), ("particle", "no"), ("conveys", "not even")] }

def all : List Datum := [ex_6a_yes, ex_6a_no, ex_6b_yes, ex_6b_no, ex_7a_yes, ex_7a_no, ex_7b_yes, ex_7b_no, ex_119_oui, ex_119_non, ex_119_si, ex_120_oui, ex_120_non, ex_120_si, ex_121_oui, ex_121_non, ex_121_si, ex_122_oui, ex_122_non, ex_122_si, ex_124_ja, ex_124_nein, ex_124_doch, ex_125_ja, ex_125_nein, ex_125_doch, ex_126_ja, ex_126_nein, ex_126_doch, ex_127_ja, ex_127_nein, ex_127_doch, ex_49_yes, ex_49_no, ex_50_yes, ex_50_no, ex_51_yes, ex_51_no, ex_52_no, ex_53_no]

end RoelofsenFarkas2015.Examples
