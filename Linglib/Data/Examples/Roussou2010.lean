module

public import Linglib.Data.Examples.Schema

/-!
# `Roussou2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Roussou2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Roussou2010.Examples`.
-/

@[expose] public section

namespace Roussou2010.Examples

def ex1a : Datum :=
  { id := "roussou2010_ex1a"
    source := ⟨"roussou-2010", "(1a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Ksero oti o Janis elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "oti")] }

def ex1a_an : Datum :=
  { id := "roussou2010_ex1a-an"
    source := ⟨"roussou-2010", "(1a-an)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Ksero an o Janis elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "an")] }

def ex1b : Datum :=
  { id := "roussou2010_ex1b"
    source := ⟨"roussou-2010", "(1b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Anarotjeme an o Janis elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "anarotjeme"), ("complementizer", "an")] }

def ex1b_oti : Datum :=
  { id := "roussou2010_ex1b-oti"
    source := ⟨"roussou-2010", "(1b-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Anarotjeme oti o Janis elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "anarotjeme"), ("complementizer", "oti")] }

def ex1c : Datum :=
  { id := "roussou2010_ex1c"
    source := ⟨"roussou-2010", "(1c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Xerome pu o Janis elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xerome"), ("complementizer", "pu")] }

def ex1c_oti : Datum :=
  { id := "roussou2010_ex1c-oti"
    source := ⟨"roussou-2010", "(1c-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Xerome oti o Janis elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xerome"), ("complementizer", "oti")] }

def ex1d : Datum :=
  { id := "roussou2010_ex1d"
    source := ⟨"roussou-2010", "(1d)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Thelo na liso to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "thelo"), ("complementizer", "na")] }

def ex1d_oti : Datum :=
  { id := "roussou2010_ex1d-oti"
    source := ⟨"roussou-2010", "(1d-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Thelo oti liso to provlima."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "thelo"), ("complementizer", "oti")] }

def ex2a : Datum :=
  { id := "roussou2010_ex2a"
    source := ⟨"roussou-2010", "(2a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Ksero na aghapao."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "na")] }

def ex2b_an : Datum :=
  { id := "roussou2010_ex2b-an"
    source := ⟨"roussou-2010", "(2b-an)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Dhen ksero an elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "an"), ("negation", "yes")] }

def ex2b_oti : Datum :=
  { id := "roussou2010_ex2b-oti"
    source := ⟨"roussou-2010", "(2b-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Dhen ksero oti elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "oti"), ("negation", "yes")] }

def ex2c_an : Datum :=
  { id := "roussou2010_ex2c-an"
    source := ⟨"roussou-2010", "(2c-an)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Kseris an elise to provlima?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "an"), ("question", "yes")] }

def ex2c_oti : Datum :=
  { id := "roussou2010_ex2c-oti"
    source := ⟨"roussou-2010", "(2c-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Kseris oti elise to provlima?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "oti"), ("question", "yes")] }

def ex3a_oti : Datum :=
  { id := "roussou2010_ex3a-oti"
    source := ⟨"roussou-2010", "(3a-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pistevo oti elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "oti")] }

def ex3a_na : Datum :=
  { id := "roussou2010_ex3a-na"
    source := ⟨"roussou-2010", "(3a-na)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pistevo na elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "na")] }

def ex3b_oti : Datum :=
  { id := "roussou2010_ex3b-oti"
    source := ⟨"roussou-2010", "(3b-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pistepsa oti elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "oti"), ("tense", "past")] }

def ex3b_na : Datum :=
  { id := "roussou2010_ex3b-na"
    source := ⟨"roussou-2010", "(3b-na)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pistepsa na elise to provlima."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "na"), ("tense", "past")] }

def ex16a : Datum :=
  { id := "roussou2010_ex16a"
    source := ⟨"roussou-2010", "(16a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis dhen pistevi oti i Maria efije."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "oti"), ("negation", "yes")] }

def ex17_oti : Datum :=
  { id := "roussou2010_ex17-oti"
    source := ⟨"roussou-2010", "(17-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Thimame oti dhjavaze poli."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "thimame"), ("complementizer", "oti")] }

def ex17_pu : Datum :=
  { id := "roussou2010_ex17-pu"
    source := ⟨"roussou-2010", "(17-pu)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Thimame pu dhjavaze poli."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "thimameStat"), ("complementizer", "pu")] }

def ex19a : Datum :=
  { id := "roussou2010_ex19a"
    source := ⟨"roussou-2010", "(19a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis paradextike oti eklepse ta lefta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "paradhexome"), ("complementizer", "oti"), ("tense", "past")] }

def ex20a : Datum :=
  { id := "roussou2010_ex20a"
    source := ⟨"roussou-2010", "(20a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis xerete pu efijes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xerome"), ("complementizer", "pu")] }

def ex20a_oti : Datum :=
  { id := "roussou2010_ex20a-oti"
    source := ⟨"roussou-2010", "(20a-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis xerete oti efijes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "xerome"), ("complementizer", "oti")] }

def ex20b_pu : Datum :=
  { id := "roussou2010_ex20b-pu"
    source := ⟨"roussou-2010", "(20b-pu)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis anisixi pu efijes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "anisixo"), ("complementizer", "pu")] }

def ex20b_oti : Datum :=
  { id := "roussou2010_ex20b-oti"
    source := ⟨"roussou-2010", "(20b-oti)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis anisixi oti efijes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "anisixo"), ("complementizer", "oti")] }

def ex22a : Datum :=
  { id := "roussou2010_ex22a"
    source := ⟨"roussou-2010", "(22a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Su IPA pu efije o Janis?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "leo"), ("complementizer", "pu"), ("question", "yes"), ("focus", "yes"), ("tense", "past")] }

def ex23c : Datum :=
  { id := "roussou2010_ex23c"
    source := ⟨"roussou-2010", "(23c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Dhen nomizo na efije noris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nomizo"), ("complementizer", "na"), ("negation", "yes")] }

def ex23c_star : Datum :=
  { id := "roussou2010_ex23c-star"
    source := ⟨"roussou-2010", "(23c-star)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Nomizo na efije noris."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "nomizo"), ("complementizer", "na")] }

def ex23d : Datum :=
  { id := "roussou2010_ex23d"
    source := ⟨"roussou-2010", "(23d)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pistepsa na efije noris."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pistevo"), ("complementizer", "na"), ("tense", "past")] }

def ex25a : Datum :=
  { id := "roussou2010_ex25a"
    source := ⟨"roussou-2010", "(25a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis kseri oti tha fiji."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "oti")] }

def ex25b : Datum :=
  { id := "roussou2010_ex25b"
    source := ⟨"roussou-2010", "(25b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis kseri na dhjavazi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "na")] }

def ex26a : Datum :=
  { id := "roussou2010_ex26a"
    source := ⟨"roussou-2010", "(26a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Thimithike na klidhosi tin porta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "thimame"), ("complementizer", "na"), ("tense", "past")] }

def ex26a_star : Datum :=
  { id := "roussou2010_ex26a-star"
    source := ⟨"roussou-2010", "(26a-star)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Thimithike na klidhose tin porta."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "thimame"), ("complementizer", "na"), ("tense", "past"), ("embeddedTense", "past")] }

def ex34 : Datum :=
  { id := "roussou2010_ex34"
    source := ⟨"roussou-2010", "(34)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis dhen kseri an perase tis eksetasis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "an"), ("negation", "yes")] }

def ex34_star : Datum :=
  { id := "roussou2010_ex34-star"
    source := ⟨"roussou-2010", "(34-star)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Janis kseri an perase tis eksetasis."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ksero"), ("complementizer", "an")] }

def all : List Datum := [ex1a, ex1a_an, ex1b, ex1b_oti, ex1c, ex1c_oti, ex1d, ex1d_oti, ex2a, ex2b_an, ex2b_oti, ex2c_an, ex2c_oti, ex3a_oti, ex3a_na, ex3b_oti, ex3b_na, ex16a, ex17_oti, ex17_pu, ex19a, ex20a, ex20a_oti, ex20b_pu, ex20b_oti, ex22a, ex23c, ex23c_star, ex23d, ex25a, ex25b, ex26a, ex26a_star, ex34, ex34_star]

end Roussou2010.Examples
