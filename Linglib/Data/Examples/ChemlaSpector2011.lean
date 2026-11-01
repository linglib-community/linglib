module

public import Linglib.Data.Examples.Schema

/-!
# `ChemlaSpector2011` — typed example data

Auto-generated from `Linglib/Data/Examples/ChemlaSpector2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChemlaSpector2011.Examples`.
-/

@[expose] public section

namespace ChemlaSpector2011.Examples

def exp1_universal_some_false : Datum :=
  { id := "chemlaspector2011_exp1_universal_some_false"
    source := ⟨"chemla-spector-2011", "(8), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "universal"), ("condition", "false"), ("rating", "120"), ("figure", "5")] }

def exp1_universal_or_false : Datum :=
  { id := "chemlaspector2011_exp1_universal_or_false"
    source := ⟨"chemla-spector-2011", "(9), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "universal"), ("condition", "false"), ("rating", "110"), ("figure", "5")] }

def exp1_universal_some_literal : Datum :=
  { id := "chemlaspector2011_exp1_universal_some_literal"
    source := ⟨"chemla-spector-2011", "(8), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "universal"), ("condition", "literal"), ("rating", "440"), ("figure", "5")] }

def exp1_universal_or_literal : Datum :=
  { id := "chemlaspector2011_exp1_universal_or_literal"
    source := ⟨"chemla-spector-2011", "(9), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "universal"), ("condition", "literal"), ("rating", "350"), ("figure", "5")] }

def exp1_universal_some_weak : Datum :=
  { id := "chemlaspector2011_exp1_universal_some_weak"
    source := ⟨"chemla-spector-2011", "(8), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "universal"), ("condition", "weak"), ("rating", "680"), ("figure", "5")] }

def exp1_universal_or_weak : Datum :=
  { id := "chemlaspector2011_exp1_universal_or_weak"
    source := ⟨"chemla-spector-2011", "(9), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "universal"), ("condition", "weak"), ("rating", "540"), ("figure", "5")] }

def exp1_universal_some_strong : Datum :=
  { id := "chemlaspector2011_exp1_universal_some_strong"
    source := ⟨"chemla-spector-2011", "(8), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "universal"), ("condition", "strong"), ("rating", "990"), ("figure", "5")] }

def exp1_universal_or_strong : Datum :=
  { id := "chemlaspector2011_exp1_universal_or_strong"
    source := ⟨"chemla-spector-2011", "(9), Figure 5"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Chaque lettre est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "universal"), ("condition", "strong"), ("rating", "860"), ("figure", "5")] }

def exp1_de_some_false : Datum :=
  { id := "chemlaspector2011_exp1_de_some_false"
    source := ⟨"chemla-spector-2011", "(12), Figure 6"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "de"), ("condition", "false"), ("rating", "65"), ("figure", "6")] }

def exp1_de_or_false : Datum :=
  { id := "chemlaspector2011_exp1_de_or_false"
    source := ⟨"chemla-spector-2011", "(13), Figure 6"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "de"), ("condition", "false"), ("rating", "90"), ("figure", "6")] }

def exp1_de_some_qlocal : Datum :=
  { id := "chemlaspector2011_exp1_de_some_qlocal"
    source := ⟨"chemla-spector-2011", "(12), Figure 6"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "de"), ("condition", "qlocal"), ("rating", "250"), ("figure", "6")] }

def exp1_de_or_qlocal : Datum :=
  { id := "chemlaspector2011_exp1_de_or_qlocal"
    source := ⟨"chemla-spector-2011", "(13), Figure 6"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "de"), ("condition", "qlocal"), ("rating", "140"), ("figure", "6")] }

def exp1_de_some_both : Datum :=
  { id := "chemlaspector2011_exp1_de_some_both"
    source := ⟨"chemla-spector-2011", "(12), Figure 6"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "some"), ("environment", "de"), ("condition", "both"), ("rating", "920"), ("figure", "6")] }

def exp1_de_or_both : Datum :=
  { id := "chemlaspector2011_exp1_de_or_both"
    source := ⟨"chemla-spector-2011", "(13), Figure 6"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "or"), ("environment", "de"), ("condition", "both"), ("rating", "930"), ("figure", "6")] }

def exp2_exactlyOne_some_false : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_some_false"
    source := ⟨"chemla-spector-2011", "(21), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "exactlyOne"), ("condition", "false"), ("rating", "67"), ("figure", "12")] }

def exp2_exactlyOne_or_false : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_or_false"
    source := ⟨"chemla-spector-2011", "(22), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "exactlyOne"), ("condition", "false"), ("rating", "91"), ("figure", "12")] }

def exp2_exactlyOne_some_literal : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_some_literal"
    source := ⟨"chemla-spector-2011", "(21), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "exactlyOne"), ("condition", "literal"), ("rating", "370"), ("figure", "12")] }

def exp2_exactlyOne_or_literal : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_or_literal"
    source := ⟨"chemla-spector-2011", "(22), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "exactlyOne"), ("condition", "literal"), ("rating", "370"), ("figure", "12")] }

def exp2_exactlyOne_some_local : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_some_local"
    source := ⟨"chemla-spector-2011", "(21), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "exactlyOne"), ("condition", "local"), ("rating", "730"), ("figure", "12")] }

def exp2_exactlyOne_or_local : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_or_local"
    source := ⟨"chemla-spector-2011", "(22), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "exactlyOne"), ("condition", "local"), ("rating", "580"), ("figure", "12")] }

def exp2_exactlyOne_some_all : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_some_all"
    source := ⟨"chemla-spector-2011", "(21), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "exactlyOne"), ("condition", "all"), ("rating", "980"), ("figure", "12")] }

def exp2_exactlyOne_or_all : Datum :=
  { id := "chemlaspector2011_exp2_exactlyOne_or_all"
    source := ⟨"chemla-spector-2011", "(22), Figure 12"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Il y a exactement une lettre reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "exactlyOne"), ("condition", "all"), ("rating", "900"), ("figure", "12")] }

def exp2_de_some_false : Datum :=
  { id := "chemlaspector2011_exp2_de_some_false"
    source := ⟨"chemla-spector-2011", "(12), Figure 13"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "de"), ("condition", "false"), ("rating", "33"), ("figure", "13")] }

def exp2_de_or_false : Datum :=
  { id := "chemlaspector2011_exp2_de_or_false"
    source := ⟨"chemla-spector-2011", "(13), Figure 13"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "de"), ("condition", "false"), ("rating", "45"), ("figure", "13")] }

def exp2_de_some_qlocal : Datum :=
  { id := "chemlaspector2011_exp2_de_some_qlocal"
    source := ⟨"chemla-spector-2011", "(12), Figure 13"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "de"), ("condition", "qlocal"), ("rating", "510"), ("figure", "13")] }

def exp2_de_or_qlocal : Datum :=
  { id := "chemlaspector2011_exp2_de_or_qlocal"
    source := ⟨"chemla-spector-2011", "(13), Figure 13"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "de"), ("condition", "qlocal"), ("rating", "220"), ("figure", "13")] }

def exp2_de_some_both : Datum :=
  { id := "chemlaspector2011_exp2_de_some_both"
    source := ⟨"chemla-spector-2011", "(12), Figure 13"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à certains de ses cercles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "some"), ("environment", "de"), ("condition", "both"), ("rating", "970"), ("figure", "13")] }

def exp2_de_or_both : Datum :=
  { id := "chemlaspector2011_exp2_de_or_both"
    source := ⟨"chemla-spector-2011", "(13), Figure 13"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1290"
    primaryText := "Aucune lettre n'est reliée à son cercle rouge ou à son cercle bleu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "or"), ("environment", "de"), ("condition", "both"), ("rating", "950"), ("figure", "13")] }

def all : List Datum := [exp1_universal_some_false, exp1_universal_or_false, exp1_universal_some_literal, exp1_universal_or_literal, exp1_universal_some_weak, exp1_universal_or_weak, exp1_universal_some_strong, exp1_universal_or_strong, exp1_de_some_false, exp1_de_or_false, exp1_de_some_qlocal, exp1_de_or_qlocal, exp1_de_some_both, exp1_de_or_both, exp2_exactlyOne_some_false, exp2_exactlyOne_or_false, exp2_exactlyOne_some_literal, exp2_exactlyOne_or_literal, exp2_exactlyOne_some_local, exp2_exactlyOne_or_local, exp2_exactlyOne_some_all, exp2_exactlyOne_or_all, exp2_de_some_false, exp2_de_or_false, exp2_de_some_qlocal, exp2_de_or_qlocal, exp2_de_some_both, exp2_de_or_both]

end ChemlaSpector2011.Examples
