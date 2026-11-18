module

public import Linglib.Data.Examples.Schema

/-!
# `Denic2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Denic2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Denic2023.Examples`.
-/

@[expose] public section

namespace Denic2023.Examples

def ex_6 : Datum :=
  { id := "denic2023_6"
    source := ⟨"denic-2023", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All 20 of Mary's friends are French or Spanish."
    glossedTokens := []
    context := "What is being discussed is where Mary's friends are from."
    judgment := .acceptable
    contrasts := []
    readings := [("distributive", .acceptable), ("ignorance", .marginal)]
    paperFeatures := [("name", "all-20-or"), ("restrictor", "20"), ("disjuncts", "2"), ("preferred", "distributive")] }

def ex_7 : Datum :=
  { id := "denic2023_7"
    source := ⟨"denic-2023", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both of Mary's friends are French or Spanish."
    glossedTokens := []
    context := "What is being discussed is where Mary's friends are from."
    judgment := .acceptable
    contrasts := []
    readings := [("distributive", .marginal), ("ignorance", .acceptable)]
    paperFeatures := [("name", "all-2-or"), ("restrictor", "2"), ("disjuncts", "2"), ("preferred", "ignorance")] }

def ex_8 : Datum :=
  { id := "denic2023_8"
    source := ⟨"denic-2023", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All four of Mary's friends are French or Spanish."
    glossedTokens := []
    context := "What is being discussed is where Mary's friends are from."
    judgment := .acceptable
    contrasts := []
    readings := [("distributive", .acceptable), ("ignorance", .marginal)]
    paperFeatures := [("name", "simple-disj"), ("restrictor", "4"), ("disjuncts", "2"), ("preferred", "distributive")] }

def ex_9 : Datum :=
  { id := "denic2023_9"
    source := ⟨"denic-2023", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All four of Mary's friends are French, Spanish, German, or Dutch."
    glossedTokens := []
    context := "What is being discussed is where Mary's friends are from."
    judgment := .acceptable
    contrasts := []
    readings := [("distributive", .marginal), ("ignorance", .acceptable)]
    paperFeatures := [("name", "complex-disj"), ("restrictor", "4"), ("disjuncts", "4"), ("preferred", "ignorance")] }

def ex_12 : Datum :=
  { id := "denic2023_12"
    source := ⟨"denic-2023", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is French or Spanish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("name", "unembedded"), ("disjuncts", "2")] }

def ex_31 : Datum :=
  { id := "denic2023_31"
    source := ⟨"denic-2023", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of those three girls is Mary, Susan, or Jane."
    glossedTokens := []
    context := "Peter invited three girls to the party."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("name", "deviant-be"), ("predicate", "identityCopula"), ("singletonDenoting", "yes")] }

def ex_32 : Datum :=
  { id := "denic2023_32"
    source := ⟨"denic-2023", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of those three girls is called Mary, Susan, or Jane."
    glossedTokens := []
    context := "Peter invited three girls to the party."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("name", "non-deviant-called"), ("predicate", "beCalled"), ("singletonDenoting", "no")] }

def ex_33 : Datum :=
  { id := "denic2023_33"
    source := ⟨"denic-2023", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of those three writers wrote Anna Karenina, Germinal, or Harry Potter."
    glossedTokens := []
    context := "Tolstoy, Zola and Rowling are great writers."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("name", "deviant-write"), ("predicate", "write"), ("singletonDenoting", "yes")] }

def ex_34 : Datum :=
  { id := "denic2023_34"
    source := ⟨"denic-2023", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of those three students read Anna Karenina, Germinal, or Harry Potter."
    glossedTokens := []
    context := "Ann, John, and Bob are great students."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("name", "non-deviant-read"), ("predicate", "read"), ("singletonDenoting", "no")] }

def ex_35 : Datum :=
  { id := "denic2023_35"
    source := ⟨"denic-2023", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "One of those three girls is Mary, another one is Susan, and yet another one is Jane."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("name", "paraphrase-of-deviant-be")] }

def ex_37a : Datum :=
  { id := "denic2023_37a"
    source := ⟨"denic-2023", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This girl is my sister Susan. That other girl is my sister Susan too."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "singletonDenoting"), ("predicate", "identityCopula")] }

def ex_37b : Datum :=
  { id := "denic2023_37b"
    source := ⟨"denic-2023", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This girl is called Susan. That other girl is called Susan too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "singletonDenoting"), ("predicate", "beCalled")] }

def ex_37c : Datum :=
  { id := "denic2023_37c"
    source := ⟨"denic-2023", "(37c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wrote this book. Peter wrote this book too."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "singletonDenoting"), ("predicate", "write")] }

def ex_37d : Datum :=
  { id := "denic2023_37d"
    source := ⟨"denic-2023", "(37d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John read this book. Peter read this book too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "singletonDenoting"), ("predicate", "read")] }

def ex_38 : Datum :=
  { id := "denic2023_38"
    source := ⟨"denic-2023", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of John's three students wrote the letter A, the letter D, or the letter K on the board."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "write"), ("singletonDenoting", "no")] }

def ex_41 : Datum :=
  { id := "denic2023_41"
    source := ⟨"magri-2009", ""⟩
    reportedIn := some ⟨"denic-2023", "(41)"⟩
    language := "stan1293"
    primaryText := "Some Italians come from a warm country."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "blindImplicature")] }

def ex_43a : Datum :=
  { id := "denic2023_43a"
    source := ⟨"buccola-haida-2019", ""⟩
    reportedIn := some ⟨"denic-2023", "(43a)"⟩
    language := "stan1293"
    primaryText := "Ann scored at least 3 points."
    glossedTokens := []
    context := "Ann played a card game in which, given the rules, the final score is always an even number of points. Bob knows this, and reports to Carl."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "blindIgnorance")] }

def ex_43b : Datum :=
  { id := "denic2023_43b"
    source := ⟨"buccola-haida-2019", ""⟩
    reportedIn := some ⟨"denic-2023", "(43b)"⟩
    language := "stan1293"
    primaryText := "Ann scored at least 4 points."
    glossedTokens := []
    context := "Ann played a card game in which, given the rules, the final score is always an even number of points. Bob knows this, and reports to Carl."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "blindIgnorance")] }

def ex_48 : Datum :=
  { id := "denic2023_48"
    source := ⟨"denic-2023", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of Mary's 5 cousins or all of her 20 friends are French."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not all of her 20 friends are French", .unacceptable)]
    paperFeatures := [("diagnostic", "symmetry")] }

def ex_55a : Datum :=
  { id := "denic2023_55a"
    source := ⟨"denic-2023", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of these three girls must be Mary, Susan, or Jane."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "modalContrast"), ("modal", "necessity")] }

def ex_55b : Datum :=
  { id := "denic2023_55b"
    source := ⟨"denic-2023", "(55b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of these three girls might be Mary, Susan, or Jane."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "modalContrast"), ("modal", "possibility")] }

def ex_57 : Datum :=
  { id := "denic2023_57"
    source := ⟨"denic-2023", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of the twenty girls in this photo is Lisa or one of our neighbors."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "largerDomain"), ("restrictor", "20")] }

def ex_59 : Datum :=
  { id := "denic2023_59"
    source := ⟨"denic-2023", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that both of these girls are Susan or Jane."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "downwardEntailing")] }

def ex_63 : Datum :=
  { id := "denic2023_63"
    source := ⟨"denic-2023", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both of Mary's office-mates are American or British."
    glossedTokens := []
    context := "Mary works in the US, so her office-mates are very likely American."
    judgment := .acceptable
    contrasts := []
    readings := [("distributive", .marginal), ("ignorance", .acceptable)]
    paperFeatures := [("diagnostic", "priorKnowledge"), ("restrictor", "2"), ("disjuncts", "2"), ("preferred", "ignorance")] }

def all : List Datum := [ex_6, ex_7, ex_8, ex_9, ex_12, ex_31, ex_32, ex_33, ex_34, ex_35, ex_37a, ex_37b, ex_37c, ex_37d, ex_38, ex_41, ex_43a, ex_43b, ex_48, ex_55a, ex_55b, ex_57, ex_59, ex_63]

end Denic2023.Examples
