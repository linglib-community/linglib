module

public import Linglib.Data.Examples.Schema

/-!
# `Lassiter2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Lassiter2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lassiter2015.Examples`.
-/

@[expose] public section

namespace Lassiter2015.Examples

def ex2b : Datum :=
  { id := "lassiter2015_ex2b"
    source := ⟨"lassiter-2015", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is as likely to win the lottery as he is not to win it."
    glossedTokens := []
    context := "A lottery with a million tickets; three siblings, Sam, Mary and Sue, buy two tickets each, and nobody else buys more than two."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ ¬φ"), ("truthValue", "false")] }

def ex4 : Datum :=
  { id := "lassiter2015_ex4"
    source := ⟨"lassiter-2015", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is as likely to win the lottery as anyone else is."
    glossedTokens := []
    context := "A lottery with a million tickets; three siblings, Sam, Mary and Sue, buy two tickets each, and nobody else buys more than two."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ ψ_i for each i"), ("truthValue", "true")] }

def ex5 : Datum :=
  { id := "lassiter2015_ex5"
    source := ⟨"lassiter-2015", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is as likely to win the lottery as Mary or Sue is."
    glossedTokens := []
    context := "The same lottery."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ ψ ∧ φ ⪰ χ"), ("truthValue", "true")] }

def ex8 : Datum :=
  { id := "lassiter2015_ex8"
    source := ⟨"lassiter-2015", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win as it is that Mary or Sue will win."
    glossedTokens := []
    context := "The same lottery."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ (ψ ∨ χ)"), ("truthValue", "false")] }

def ex9 : Datum :=
  { id := "lassiter2015_ex9"
    source := ⟨"lassiter-2015", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win as it is that one of his sisters will win."
    glossedTokens := []
    context := "The same lottery."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ (ψ ∨ χ)"), ("truthValue", "false")] }

def ex12 : Datum :=
  { id := "lassiter2015_ex12"
    source := ⟨"lassiter-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win as it is that Mary, Sue, Tom, Alice, Bob, Hank or Murray will."
    glossedTokens := []
    context := "The lottery, with five more people holding two tickets each."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ (ψ₁ ∨ … ∨ ψ₇)"), ("truthValue", "false")] }

def ex33c : Datum :=
  { id := "lassiter2015_ex33c"
    source := ⟨"lassiter-2015", "(33c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win (and Mary and Sue will not) as it is that either Mary or Sue will win (and Sam will not)."
    glossedTokens := []
    context := "The lottery with three siblings."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.4"), ("form", "(φ ∧ ¬ψ ∧ ¬χ) ⪰ ((¬φ ∧ ψ ∧ ¬χ) ∨ (¬φ ∧ ¬ψ ∧ χ))"), ("truthValue", "false")] }

def ex35 : Datum :=
  { id := "lassiter2015_ex35"
    source := ⟨"lassiter-2015", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If φ must be the case, then φ is more likely than ¬φ."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.5"), ("pattern", "must to more likely than not")] }

def ex48 : Datum :=
  { id := "lassiter2015_ex48"
    source := ⟨"lassiter-2015", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is exactly as likely that Sam will go to the movies as it is that he will either go to school or go to the movies."
    glossedTokens := []
    context := "Sam might go to school, but he is somewhat more likely to cut class and go to the movies."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("measure", "symmetric fuzzy"), ("truthValue", "false")] }

def ex50 : Datum :=
  { id := "lassiter2015_ex50"
    source := ⟨"lassiter-2015", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are exactly three times as likely to throw an odd number as you are to throw a two."
    glossedTokens := []
    context := "You are about to throw a fair die."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio")] }

def ex51 : Datum :=
  { id := "lassiter2015_ex51"
    source := ⟨"lassiter-2015", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are exactly twice as likely to draw a jack as you are to draw a red queen."
    glossedTokens := []
    context := "You are about to draw a card at random from a well-shuffled pack."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio")] }

def ex53 : Datum :=
  { id := "lassiter2015_ex53"
    source := ⟨"lassiter-2015", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is exactly three times as tall as Bill is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio"), ("scale", "additive")] }

def ex54 : Datum :=
  { id := "lassiter2015_ex54"
    source := ⟨"lassiter-2015", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is exactly three times as angry as Bill is."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio"), ("scale", "non-additive")] }

def ex56 : Datum :=
  { id := "lassiter2015_ex56"
    source := ⟨"lassiter-2015", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam must be at home. Therefore it is much more likely that Sam is at home than it is that he is not at home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("pattern", "must to much more likely than not")] }

def ex62 : Datum :=
  { id := "lassiter2015_ex62"
    source := ⟨"lassiter-2015", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[T]he 1880 census shows her living with mom, two brothers and her daughter … So David [the father] must have died before 1880."
    glossedTokens := []
    context := "An online genealogy discussion; David is the father."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("issue", "weakness of must")] }

def ex65a : Datum :=
  { id := "lassiter2015_ex65a"
    source := ⟨"lassiter-2015", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yale is more likely to win the NCAA basketball championship than Harvard is."
    glossedTokens := []
    context := "A year in which Yale is a much better team than Harvard, and the odds against either winning are astronomical."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "more likely than to might")] }

def ex65b : Datum :=
  { id := "lassiter2015_ex65b"
    source := ⟨"lassiter-2015", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yale might win the NCAA basketball championship."
    glossedTokens := []
    context := "The same year."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "more likely than to might")] }

def all : List Datum := [ex2b, ex4, ex5, ex8, ex9, ex12, ex33c, ex35, ex48, ex50, ex51, ex53, ex54, ex56, ex62, ex65a, ex65b]

end Lassiter2015.Examples
