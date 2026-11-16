module

public import Linglib.Data.Examples.Schema

/-!
# `Chatain2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Chatain2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chatain2025.Examples`.
-/

@[expose] public section

namespace Chatain2025.Examples

def ex_2a : Datum :=
  { id := "chatain2025_2a"
    source := ⟨"chatain-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There isn't a phone-book and it is in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "negated antecedent, conjunction")] }

def ex_3a : Datum :=
  { id := "chatain2025_3a"
    source := ⟨"chatain-2025", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a phone-book. It is in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "cross-sentential")] }

def ex_3b : Datum :=
  { id := "chatain2025_3b"
    source := ⟨"chatain-2025", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a phone-book and it is in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "conjunction")] }

def ex_3c : Datum :=
  { id := "chatain2025_3c"
    source := ⟨"chatain-2025", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there isn't a phone-book or it is in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "bathroom disjunction")] }

def ex_3d : Datum :=
  { id := "chatain2025_3d"
    source := ⟨"chatain-2025", "(3d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there is a phone-book, it is in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "conditional")] }

def ex_3e : Datum :=
  { id := "chatain2025_3e"
    source := ⟨"chatain-2025", "(3e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is in the cabinet and there is a phone-book."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "conjunction, pronoun first")] }

def ex_3f : Datum :=
  { id := "chatain2025_3f"
    source := ⟨"chatain-2025", "(3f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there is a phone-book or it is in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "disjunction")] }

def ex_3g : Datum :=
  { id := "chatain2025_3g"
    source := ⟨"chatain-2025", "(3g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it is a phone-book, there is a phone-book."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "conditional, pronoun first")] }

def ex_55c : Datum :=
  { id := "chatain2025_55c"
    source := ⟨"chatain-2025", "(55c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There might be a phone-book. It would be in the cabinet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "modal subordination")] }

def ex_55d : Datum :=
  { id := "chatain2025_55d"
    source := ⟨"chatain-2025", "(55d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not available at the library now but there is a phone-book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "but-conjunction, pronoun first")] }

def ex_78a : Datum :=
  { id := "chatain2025_78a"
    source := ⟨"chatain-2025", "(78a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only nine out of the ten marbles have been found. We're still looking for it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "no antecedent")] }

def ex_79a : Datum :=
  { id := "chatain2025_79a"
    source := ⟨"chatain-2025", "(79a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every tourist bought a ticket. Most have already used it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "quantificational subordination")] }

def ex_79b : Datum :=
  { id := "chatain2025_79b"
    source := ⟨"chatain-2025", "(79b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every tourist who bought a ticket has already used it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("existential", .acceptable), ("universal", .acceptable)]
    paperFeatures := [("configuration", "donkey")] }

def ex_113b : Datum :=
  { id := "chatain2025_113b"
    source := ⟨"chatain-2025", "(113b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every tourist bought a ticket. Most French tourists have already used it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "quantificational subordination")] }

def ex_113c : Datum :=
  { id := "chatain2025_113c"
    source := ⟨"chatain-2025", "(113c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every tourist bought a ticket. Most locals have already used it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("configuration", "quantificational subordination")] }

def all : List Datum := [ex_2a, ex_3a, ex_3b, ex_3c, ex_3d, ex_3e, ex_3f, ex_3g, ex_55c, ex_55d, ex_78a, ex_79a, ex_79b, ex_113b, ex_113c]

end Chatain2025.Examples
