module

public import Linglib.Data.Examples.Schema

/-!
# `Williams2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Williams2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Williams2025.Examples`.
-/

@[expose] public section

namespace Williams2025.Examples

def ex_4 : Datum :=
  { id := "williams2025_4"
    source := ⟨"williams-2025", "(4)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot that he stopped by the flower shop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "cognition"), ("presupposition", "John stopped by the flower shop")] }

def ex_5 : Datum :=
  { id := "williams2025_5"
    source := ⟨"williams-2025", "(5)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot to stop by the flower shop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "psych-action"), ("presupposition", "John was supposed to stop by the flower shop"), ("presupposition", "If John stopped by the flowershop, it is because he remembered to do it.")] }

def ex_7a : Datum :=
  { id := "williams2025_7a"
    source := ⟨"williams-2025", "(7a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot stopping by the flowershop but he did not have to stop by the flowershop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_8a : Datum :=
  { id := "williams2025_8a"
    source := ⟨"williams-2025", "(8a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot having stopped by the flower shop but he did not have to stop by the flower shop"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_9a : Datum :=
  { id := "williams2025_9a"
    source := ⟨"williams-2025", "(9a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot stopping by the flower shop but he didn't stop by the flower shop"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_10a : Datum :=
  { id := "williams2025_10a"
    source := ⟨"williams-2025", "(10a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot having stopped by the flower shop but he didn't stop by the flower shop"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11a : Datum :=
  { id := "williams2025_11a"
    source := ⟨"williams-2025", "(11a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan olvidó que pasó por la floristería pero no tenía por qué pasar por la floristería"
    glossedTokens := [("Juan", "Juan"), ("olvidó", "forgot"), ("que", "that"), ("pasó", "he.passed"), ("por", "by"), ("la", "the"), ("floristería", "flowershop"), ("pero", "but"), ("no", "NEG"), ("tenía", "have.to"), ("por", "for"), ("qué", "that"), ("pasar", "to.pass"), ("por", "by"), ("la", "the"), ("floristería", "flowershop")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "williams2025_12a"
    source := ⟨"williams-2025", "(12a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan olvidó pasar por la floristería pero no tenía por qué pasar por la floristería"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13a : Datum :=
  { id := "williams2025_13a"
    source := ⟨"williams-2025", "(13a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan olvidó haber pasado por la floristería pero no tenía por qué pasar por la floristería"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "williams2025_14a"
    source := ⟨"williams-2025", "(14a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan olvidó haber pasado por la floristería pero no pasó por la floristería"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn5_i : Datum :=
  { id := "williams2025_fn5_i"
    source := ⟨"williams-2025", "fn. 5 (i)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John forgot to have stopped by the flower shop."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("John claimed to have stopped by the flower shop.", .acceptable)]
    readings := []
    paperFeatures := [] }

def ex_18a : Datum :=
  { id := "williams2025_18a"
    source := ⟨"williams-2025", "(18a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "On Tuesday, Mary forgot that she called back her twin. On Monday, Mary began to call back her twin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_18b : Datum :=
  { id := "williams2025_18b"
    source := ⟨"williams-2025", "(18b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "On Tuesday, Mary forgot that she called back her twin. On Wednesday, Mary began to call back her twin."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19a : Datum :=
  { id := "williams2025_19a"
    source := ⟨"williams-2025", "(19a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "On Tuesday, Mary forgot calling back her twin. On Monday, Mary began to call back her twin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19b : Datum :=
  { id := "williams2025_19b"
    source := ⟨"williams-2025", "(19b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "On Tuesday, Mary forgot calling back her twin. On Wednesday, Mary began to call back her twin."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20a : Datum :=
  { id := "williams2025_20a"
    source := ⟨"williams-2025", "(20a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "María olvidó haber devuelto la llamada a su gemela. El lunes, María comenzó a devolverle la llamada a su gemela."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20b : Datum :=
  { id := "williams2025_20b"
    source := ⟨"williams-2025", "(20b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "María olvidó haber devuelto la llamada a su gemela. El miércoles, María comenzó a devolverle la llamada a su gemela."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21a : Datum :=
  { id := "williams2025_21a"
    source := ⟨"williams-2025", "(21a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "On Tuesday, Mary forgot to call back her twin. On Monday, Mary's twin told her to call her back."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21b : Datum :=
  { id := "williams2025_21b"
    source := ⟨"williams-2025", "(21b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "On Tuesday, Mary forgot to call back her twin. On Wednesday, Mary's twin told her to call her back."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_4, ex_5, ex_7a, ex_8a, ex_9a, ex_10a, ex_11a, ex_12a, ex_13a, ex_14a, fn5_i, ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b, ex_21a, ex_21b]

end Williams2025.Examples
