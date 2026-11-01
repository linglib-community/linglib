module

public import Linglib.Data.Examples.Schema

/-!
# `Karttunen1971b` — typed example data

Auto-generated from `Linglib/Data/Examples/Karttunen1971b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Karttunen1971b.Examples`.
-/

@[expose] public section

namespace Karttunen1971b.Examples

def ex_2a : Datum :=
  { id := "karttunen1971b_2a"
    source := ⟨"karttunen-1971b", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill regrets that Sheila is no longer young."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "atomic"), ("projective", "yes"), ("person", "3")] }

def ex_2b : Datum :=
  { id := "karttunen1971b_2b"
    source := ⟨"karttunen-1971b", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill doesn't regret that Sheila is no longer young."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")] }

def ex_2c : Datum :=
  { id := "karttunen1971b_2c"
    source := ⟨"karttunen-1971b", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does Bill regret that Sheila is no longer young?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "3")] }

def ex_22a : Datum :=
  { id := "karttunen1971b_22a"
    source := ⟨"karttunen-1971b", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't regret that he had not told the truth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")] }

def ex_22b : Datum :=
  { id := "karttunen1971b_22b"
    source := ⟨"karttunen-1971b", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't realize that he had not told the truth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")] }

def ex_22c : Datum :=
  { id := "karttunen1971b_22c"
    source := ⟨"karttunen-1971b", "(22c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't discover that he had not told the truth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "3")] }

def ex_23 : Datum :=
  { id := "karttunen1971b_23"
    source := ⟨"karttunen-1971b", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John DIDN'T regret that he had not told the truth."
    glossedTokens := []
    context := "An emphatic denial of somebody else's previous assertion; continued 'How could he have done that when he knew that what he had said was true?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "denial"), ("environment", "negation"), ("projective", "no"), ("person", "3")] }

def ex_24a : Datum :=
  { id := "karttunen1971b_24a"
    source := ⟨"karttunen-1971b", "(24a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Did you regret that you had not told the truth?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "2")] }

def ex_24b : Datum :=
  { id := "karttunen1971b_24b"
    source := ⟨"karttunen-1971b", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you realize that you had not told the truth?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "question"), ("person", "2")] }

def ex_24c : Datum :=
  { id := "karttunen1971b_24c"
    source := ⟨"karttunen-1971b", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you discover that you had not told the truth?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "no"), ("person", "2")] }

def ex_25a : Datum :=
  { id := "karttunen1971b_25a"
    source := ⟨"karttunen-1971b", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I regret later that I have not told the truth, I will confess it to everyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "yes"), ("person", "1")] }

def ex_25b : Datum :=
  { id := "karttunen1971b_25b"
    source := ⟨"karttunen-1971b", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I realize later that I have not told the truth, I will confess it to everyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "no"), ("person", "1")] }

def ex_25c : Datum :=
  { id := "karttunen1971b_25c"
    source := ⟨"karttunen-1971b", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I discover later that I have not told the truth, I will confess it to everyone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("projective", "no"), ("person", "1")] }

def ex_26a : Datum :=
  { id := "karttunen1971b_26a"
    source := ⟨"karttunen-1971b", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that I will regret later that I have not told the truth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("projective", "yes"), ("person", "1")] }

def ex_26b : Datum :=
  { id := "karttunen1971b_26b"
    source := ⟨"karttunen-1971b", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that I will realize later that I have not told the truth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "realize"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("projective", "no"), ("person", "1")] }

def ex_26c : Datum :=
  { id := "karttunen1971b_26c"
    source := ⟨"karttunen-1971b", "(26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible that I will discover later that I have not told the truth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "discover"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("projective", "no"), ("person", "1")] }

def all : List Datum := [ex_2a, ex_2b, ex_2c, ex_22a, ex_22b, ex_22c, ex_23, ex_24a, ex_24b, ex_24c, ex_25a, ex_25b, ex_25c, ex_26a, ex_26b, ex_26c]

end Karttunen1971b.Examples
