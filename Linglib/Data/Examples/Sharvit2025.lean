module

public import Linglib.Data.Examples.Schema

/-!
# `Sharvit2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Sharvit2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sharvit2025.Examples`.
-/

@[expose] public section

namespace Sharvit2025.Examples

def ex5a : Datum :=
  { id := "sharvit2025_ex5a"
    source := ⟨"sharvit-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia has money and she is proud of her money, Sue is jealous."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "and"), ("presuppositionalClause", "second"), ("redundant", "no")] }

def ex5b : Datum :=
  { id := "sharvit2025_ex5b"
    source := ⟨"sharvit-2025", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is proud of her money and she has money, Sue is jealous."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "and"), ("presuppositionalClause", "first"), ("redundant", "yes")] }

def ex9a : Datum :=
  { id := "sharvit2025_ex9a"
    source := ⟨"sharvit-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia has money, she is proud of her money."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "if"), ("presuppositionalClause", "second"), ("redundant", "no")] }

def ex9b : Datum :=
  { id := "sharvit2025_ex9b"
    source := ⟨"sharvit-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is proud of her money, she has money."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "if"), ("presuppositionalClause", "first"), ("redundant", "yes")] }

def ex10a : Datum :=
  { id := "sharvit2025_ex10a"
    source := ⟨"sharvit-2025", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mia has money and she is proud of her money."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "and"), ("presuppositionalClause", "second"), ("redundant", "no")] }

def ex10b : Datum :=
  { id := "sharvit2025_ex10b"
    source := ⟨"sharvit-2025", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mia is proud of her money and she has money."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "and"), ("presuppositionalClause", "first"), ("redundant", "yes")] }

def ex11a : Datum :=
  { id := "sharvit2025_ex11a"
    source := ⟨"sharvit-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Either) Mia has no money or she is proud of her money."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "or"), ("presuppositionalClause", "second"), ("redundant", "no")] }

def ex11b : Datum :=
  { id := "sharvit2025_ex11b"
    source := ⟨"sharvit-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Either) Mia is proud of her money or she has no money."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "or"), ("presuppositionalClause", "first"), ("redundant", "no")] }

def ex30 : Datum :=
  { id := "sharvit2025_ex30"
    source := ⟨"sharvit-2025", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is bored or penniless, then Sue is (too)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("if-over-∃: if Mia is bored or penniless, Sue is bored or penniless", .acceptable), ("∀-over-if: if Mia is bored, Sue is bored, and if Mia is penniless, Sue is penniless", .acceptable)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "yes"), ("presuppositionalDisjunct", "no")] }

def ex34 : Datum :=
  { id := "sharvit2025_ex34"
    source := ⟨"sharvit-2025", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is bored or penniless, then Sue is bored or penniless."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("if-over-∃: if Mia is bored or penniless, Sue is bored or penniless", .acceptable), ("∀-over-if: if Mia is bored, Sue is bored, and if Mia is penniless, Sue is penniless", .ungrammatical)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "no"), ("presuppositionalDisjunct", "no")] }

def ex48 : Datum :=
  { id := "sharvit2025_ex48"
    source := ⟨"sharvit-2025", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is (either) penniless or proud of her money, then Sue is (too)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("if-over-∃: if Mia is penniless or proud of her money, Sue is penniless or proud of hers", .acceptable), ("∀-over-if: if Mia is penniless, Sue is penniless, and if Mia is proud of her money, Sue is proud of hers; presupposes that Sue has money if Mia does", .acceptable)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "yes"), ("presuppositionalDisjunct", "yes")] }

def ex50 : Datum :=
  { id := "sharvit2025_ex50"
    source := ⟨"sharvit-2025", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is penniless or proud of her money, then Sue is penniless or proud of her money."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("if-over-∃: if Mia is penniless or proud of her money, Sue is penniless or proud of hers", .acceptable), ("∀-over-if: if Mia is penniless, Sue is penniless, and if Mia is proud of her money, Sue is proud of hers", .ungrammatical)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "no"), ("presuppositionalDisjunct", "yes")] }

def ex63b : Datum :=
  { id := "sharvit2025_ex63b"
    source := ⟨"sharvit-2025", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is proud of her money or penniless, then Sue is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("if-over-∃: if Mia is penniless or proud of her money, Sue is penniless or proud of hers", .acceptable), ("∀-over-if: if Mia is penniless, Sue is penniless, and if Mia is proud of her money, Sue is proud of hers; presupposes that Sue has money if Mia does", .acceptable)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "yes"), ("presuppositionalDisjunct", "yes")] }

def ex148a : Datum :=
  { id := "sharvit2025_ex148a"
    source := ⟨"sharvit-2025", "(148a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is ashamed of her children or proud of her money, then Sue is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∀-over-if, equivalent to that of (148b)", .acceptable)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "yes"), ("presuppositionalDisjunct", "both")] }

def ex148b : Datum :=
  { id := "sharvit2025_ex148b"
    source := ⟨"sharvit-2025", "(148b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mia is proud of her money or ashamed of her children, then Sue is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∀-over-if, equivalent to that of (148a)", .acceptable)]
    paperFeatures := [("construction", "roothPartee"), ("ellipsis", "yes"), ("presuppositionalDisjunct", "both")] }

def all : List Datum := [ex5a, ex5b, ex9a, ex9b, ex10a, ex10b, ex11a, ex11b, ex30, ex34, ex48, ex50, ex63b, ex148a, ex148b]

end Sharvit2025.Examples
