module

public import Linglib.Data.Examples.Schema

/-!
# `Belnap1982` — typed example data

Auto-generated from `Linglib/Data/Examples/Belnap1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belnap1982.Examples`.
-/

@[expose] public section

namespace Belnap1982.Examples

def ex_1 : Datum :=
  { id := "belnap1982_1"
    source := ⟨"belnap-1982", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which person kicked Sam?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("answers: John / It was John / The person who kicked Sam was John", .acceptable), ("non-answers: *He / *Sam kicked John / *China is populous", .ungrammatical), ("responses but not answers: I don't know / Ask Sam", .marginal)]
    paperFeatures := [("claim", "answerhood is as entrenched as sentencehood")] }

def gas : Datum :=
  { id := "belnap1982_gas"
    source := ⟨"belnap-1982", "p. 172"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where is a place at which I can get gas on a Sunday?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Unique Answer Fallacy"), ("answers", "multiple, each full and complete and true")] }

def basket : Datum :=
  { id := "belnap1982_basket"
    source := ⟨"belnap-1982", "p. 172"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What's in the basket?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Unique Answer Fallacy"), ("answers", "multiple, each full and complete and true")] }

def prime : Datum :=
  { id := "belnap1982_prime"
    source := ⟨"belnap-1982", "p. 174"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What's an example of a prime between 10 and 20?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Unique Answer Fallacy"), ("target", "Karttunen-style unique denotations")] }

def unicorns : Datum :=
  { id := "belnap1982_unicorns"
    source := ⟨"belnap-1982", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders where two unicorns live."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("for each of two actual unicorns, John wonders where it lives", .acceptable), ("John wonders where the single place is at which two unicorns live", .acceptable), ("quantifier between wonder and the wh: each unicorn possibly living in a different place", .acceptable)]
    paperFeatures := [("phenomenon", "quantifying into questions")] }

def grades : Datum :=
  { id := "belnap1982_grades"
    source := ⟨"belnap-1982", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the average grade is depends only on what grade each student receives."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "quantifying into questions"), ("embedding", "depend")] }

def king : Datum :=
  { id := "belnap1982_king"
    source := ⟨"belnap-1982", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "whether the king of France is bald"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "quantifying into a whether"), ("status", "no true answers")] }

def china : Datum :=
  { id := "belnap1982_china"
    source := ⟨"belnap-1982", "p. 177"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter knows that China is populous but he doesn't know which person kicked Sam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Distributivity Test"), ("verdict", "consistent, so not an answer")] }

def redhead : Datum :=
  { id := "belnap1982_redhead"
    source := ⟨"belnap-1982", "p. 177"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary remembered that a redhead kicked Sam, but Mary didn't remember which person kicked Sam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Distributivity Test"), ("verdict", "consistent, so not an answer")] }

def john : Datum :=
  { id := "belnap1982_john"
    source := ⟨"belnap-1982", "p. 177"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter knows that the person who kicked Sam is John but Peter doesn't know who kicked Sam."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Distributivity Test"), ("verdict", "inconsistent — likely an answer, not guaranteed")] }

def mary : Datum :=
  { id := "belnap1982_mary"
    source := ⟨"belnap-1982", "p. 192"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter knows that Mary loves John but Peter doesn't know which man Mary loves."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Distributivity Test"), ("verdict", "consistent, so not an answer")] }

def all : List Datum := [ex_1, gas, basket, prime, unicorns, grades, king, china, redhead, john, mary]

end Belnap1982.Examples
