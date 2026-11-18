module

public import Linglib.Data.Examples.Schema

/-!
# `EvcenBaleBarner2026` — typed example data

Auto-generated from `Linglib/Data/Examples/EvcenBaleBarner2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace EvcenBaleBarner2026.Examples`.
-/

@[expose] public section

namespace EvcenBaleBarner2026.Examples

def ex_1a : Datum :=
  { id := "evcenbalebarner2026_1a"
    source := ⟨"evcen-bale-barner-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary mowed the lawn."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "evcenbalebarner2026_1b"
    source := ⟨"evcen-bale-barner-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter mowed the lawn."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_1c : Datum :=
  { id := "evcenbalebarner2026_1c"
    source := ⟨"evcen-bale-barner-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paul mowed the lawn."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "evcenbalebarner2026_2a"
    source := ⟨"evcen-bale-barner-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary mows the lawn, she will receive $5."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2b : Datum :=
  { id := "evcenbalebarner2026_2b"
    source := ⟨"evcen-bale-barner-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary does the dishes, she will receive $5."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_2c : Datum :=
  { id := "evcenbalebarner2026_2c"
    source := ⟨"evcen-bale-barner-2026", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary cleans the pool, she will receive $5."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_3a : Datum :=
  { id := "evcenbalebarner2026_3a"
    source := ⟨"evcen-bale-barner-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who mowed the lawn?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_3b : Datum :=
  { id := "evcenbalebarner2026_3b"
    source := ⟨"evcen-bale-barner-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did Mary do after doing the dishes?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_3c : Datum :=
  { id := "evcenbalebarner2026_3c"
    source := ⟨"evcen-bale-barner-2026", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Mary mow the lawn?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def exp1_antecedent : Datum :=
  { id := "evcenbalebarner2026_exp1_antecedent"
    source := ⟨"evcen-bale-barner-2026", "Experiment 1, antecedent-focused"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    glossedTokens := []
    context := "Mary has tested all three buttons. Which of these buttons will play a dog sound?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("qud", "antecedentFocused"), ("tested", "all"), ("response", "no")] }

def exp1_consequent : Datum :=
  { id := "evcenbalebarner2026_exp1_consequent"
    source := ⟨"evcen-bale-barner-2026", "Experiment 1, consequent-focused"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    glossedTokens := []
    context := "Mary has tested all three buttons. What will happen if I press the blue button?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("qud", "consequentFocused"), ("tested", "all"), ("response", "cantTell")] }

def exp1_neutral : Datum :=
  { id := "evcenbalebarner2026_exp1_neutral"
    source := ⟨"evcen-bale-barner-2026", "Experiment 1, neutral"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    glossedTokens := []
    context := "Mary has tested all three buttons. What will happen if I press the buttons?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("qud", "neutral"), ("tested", "all"), ("response", "cantTell")] }

def exp3_full : Datum :=
  { id := "evcenbalebarner2026_exp3_full"
    source := ⟨"evcen-bale-barner-2026", "Experiment 3, full knowledge"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    glossedTokens := []
    context := "Mary has tested all three buttons. Which of these buttons will play a dog sound?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("qud", "antecedentFocused"), ("tested", "all"), ("response", "no")] }

def exp3_partial : Datum :=
  { id := "evcenbalebarner2026_exp3_partial"
    source := ⟨"evcen-bale-barner-2026", "Experiment 3, partial knowledge"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue button, it will play a dog barking."
    glossedTokens := []
    context := "Mary has tested the red and blue buttons only. Which of these buttons will play a dog sound?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("qud", "antecedentFocused"), ("tested", "two"), ("response", "cantTell")] }

def exp2_optimal : Datum :=
  { id := "evcenbalebarner2026_exp2_optimal"
    source := ⟨"evcen-bale-barner-2026", "Experiment 2, optimally informative"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the triangles, it will play a dog barking."
    glossedTokens := []
    context := "Which of these shapes, triangles or squares, will play a dog barking?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answerType", "optimallyInformative"), ("response", "no")] }

def exp2_overly : Datum :=
  { id := "evcenbalebarner2026_exp2_overly"
    source := ⟨"evcen-bale-barner-2026", "Experiment 2, overly informative"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the blue square, it will play a dog barking."
    glossedTokens := []
    context := "Which of these shapes, triangles or squares, will play a dog barking?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("answerType", "overlyInformative"), ("response", "no")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_2a, ex_2b, ex_2c, ex_3a, ex_3b, ex_3c, exp1_antecedent, exp1_consequent, exp1_neutral, exp3_full, exp3_partial, exp2_optimal, exp2_overly]

end EvcenBaleBarner2026.Examples
