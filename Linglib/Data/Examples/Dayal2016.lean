module

public import Linglib.Data.Examples.Schema

/-!
# `Dayal2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Dayal2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dayal2016.Examples`.
-/

@[expose] public section

namespace Dayal2016.Examples

def ex33a : Datum :=
  { id := "dayal2016_ex33a"
    source := ⟨"dayal-2016", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where did you go? What did you buy?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("construction", "sequence")] }

def ex33b : Datum :=
  { id := "dayal2016_ex33b"
    source := ⟨"dayal-2016", "(33b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What do you think? What should we buy?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("construction", "scopeMarking")] }

def ex33c : Datum :=
  { id := "dayal2016_ex33c"
    source := ⟨"dayal-2016", "(33c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What do you think we should buy?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("construction", "extraction")] }

def ex34a : Datum :=
  { id := "dayal2016_ex34a"
    source := ⟨"dayal-2016", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What does John think? Where is Mary?"
    glossedTokens := []
    context := "Mary is in Paris; John thinks she is in London."
    judgment := .acceptable
    alternatives := [("John thinks Mary is in London.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2.2"), ("construction", "scopeMarking")] }

def ex39a : Datum :=
  { id := "dayal2016_ex39a"
    source := ⟨"dayal-2016", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is certain who was at the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.3"), ("veridical", "false")] }

def ex39b : Datum :=
  { id := "dayal2016_ex39b"
    source := ⟨"dayal-2016", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary agree who was at the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.3"), ("veridical", "false")] }

def ex41a_42a : Datum :=
  { id := "dayal2016_ex41a_42a"
    source := ⟨"dayal-2016", "(41a)/(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which woman does John like? John likes Mary."
    glossedTokens := []
    context := "John likes exactly one woman, Mary."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("whNumber", "singular"), ("situation", "one")] }

def ex41a_42b : Datum :=
  { id := "dayal2016_ex41a_42b"
    source := ⟨"dayal-2016", "(41a)/(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which woman does John like? John likes Mary and Sue."
    glossedTokens := []
    context := "John likes two women, Mary and Sue."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("whNumber", "singular"), ("situation", "two")] }

def ex41b_42a : Datum :=
  { id := "dayal2016_ex41b_42a"
    source := ⟨"dayal-2016", "(41b)/(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which women does John like? John likes Mary."
    glossedTokens := []
    context := "John likes exactly one woman, Mary."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("whNumber", "plural"), ("situation", "one")] }

def ex41b_42b : Datum :=
  { id := "dayal2016_ex41b_42b"
    source := ⟨"dayal-2016", "(41b)/(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which women does John like? John likes Mary and Sue."
    glossedTokens := []
    context := "John likes two women, Mary and Sue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("whNumber", "plural"), ("situation", "two")] }

def ex41c_42a : Datum :=
  { id := "dayal2016_ex41c_42a"
    source := ⟨"dayal-2016", "(41c)/(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who does John like? John likes Mary."
    glossedTokens := []
    context := "John likes exactly one woman, Mary."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("whNumber", "neutral"), ("situation", "one")] }

def ex41c_42b : Datum :=
  { id := "dayal2016_ex41c_42b"
    source := ⟨"dayal-2016", "(41c)/(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who does John like? John likes Mary and Sue."
    glossedTokens := []
    context := "John likes two women, Mary and Sue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("whNumber", "neutral"), ("situation", "two")] }

def ex47a : Datum :=
  { id := "dayal2016_ex47a"
    source := ⟨"dayal-2016", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How tall is Marcus?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "negativeIsland")] }

def ex47b : Datum :=
  { id := "dayal2016_ex47b"
    source := ⟨"dayal-2016", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How tall isn't Marcus?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "negativeIsland")] }

def ex51a_singular : Datum :=
  { id := "dayal2016_ex51a_singular"
    source := ⟨"dayal-2016", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John like which woman?"
    glossedTokens := []
    context := "Two women in the domain, Mary and Sue."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.3"), ("whNumber", "singular"), ("construction", "polarWh")] }

def ex51a_plural : Datum :=
  { id := "dayal2016_ex51a_plural"
    source := ⟨"dayal-2016", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John like which women?"
    glossedTokens := []
    context := "Two women in the domain, Mary and Sue."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.3"), ("whNumber", "plural"), ("construction", "polarWh")] }

def ex53a : Datum :=
  { id := "dayal2016_ex53a"
    source := ⟨"beck-rullmann-1999", "(13)"⟩
    reportedIn := some ⟨"dayal-2016", "(53a)"⟩
    language := "stan1293"
    primaryText := "How many eggs are sufficient to bake this cake?"
    glossedTokens := []
    context := "Two eggs are sufficient."
    judgment := .acceptable
    alternatives := [("Two eggs are sufficient.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.3.3"), ("scale", "upward")] }

def ex53c : Datum :=
  { id := "dayal2016_ex53c"
    source := ⟨"dayal-2016", "(53c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many people left?"
    glossedTokens := []
    context := "Three people left."
    judgment := .acceptable
    alternatives := [("Three people left.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.3.3"), ("scale", "downward")] }

def ex54a : Datum :=
  { id := "dayal2016_ex54a"
    source := ⟨"beck-rullmann-1999", "(89)"⟩
    reportedIn := some ⟨"dayal-2016", "(54a)"⟩
    language := "stan1293"
    primaryText := "John knew only one answer to the question which Dutch Olympic athletes won a medal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.3"), ("whNumber", "plural"), ("construction", "answerNoun")] }

def ex54b : Datum :=
  { id := "dayal2016_ex54b"
    source := ⟨"dayal-2016", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knew only one answer to the question which Dutch Olympic athlete won a medal."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.3"), ("whNumber", "singular"), ("construction", "answerNoun")] }

def ex55a : Datum :=
  { id := "dayal2016_ex55a"
    source := ⟨"dayal-2016", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who does every man love?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Bill loves Mary and John loves Sue.", .acceptable)]
    readings := [("pair-list", .acceptable)]
    paperFeatures := [("section", "2.3.3"), ("phenomenon", "pairList"), ("quantifier", "universal")] }

def ex55b : Datum :=
  { id := "dayal2016_ex55b"
    source := ⟨"dayal-2016", "(55b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who do these men love?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Bill loves Mary and John loves Sue.", .acceptable)]
    readings := [("pair-list", .acceptable)]
    paperFeatures := [("section", "2.3.3"), ("phenomenon", "pairList"), ("quantifier", "definitePlural")] }

def ex56a : Datum :=
  { id := "dayal2016_ex56a"
    source := ⟨"dayal-2016", "(56a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who knows where Mary bought which book?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Bill knows where Mary bought Emma and John knows where she bought Persuasion.", .acceptable)]
    readings := [("pair-list", .acceptable)]
    paperFeatures := [("section", "2.3.3"), ("phenomenon", "pairList"), ("embedded", "whInSitu")] }

def ex56b : Datum :=
  { id := "dayal2016_ex56b"
    source := ⟨"dayal-2016", "(56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who knows where Mary bought these books?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Bill knows where Mary bought Emma and John knows where she bought Persuasion.", .acceptable)]
    readings := [("pair-list", .acceptable)]
    paperFeatures := [("section", "2.3.3"), ("phenomenon", "pairList"), ("embedded", "definitePlural")] }

def ex57a : Datum :=
  { id := "dayal2016_ex57a"
    source := ⟨"dayal-2016", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Speaker A: Who left the party? Speaker B: No one."
    glossedTokens := []
    context := "No one left the party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "denied"), ("speaker", "other"), ("cleft", "false")] }

def ex57b : Datum :=
  { id := "dayal2016_ex57b"
    source := ⟨"karttunen-peters-1976", "p. 355"⟩
    reportedIn := some ⟨"dayal-2016", "(57b)"⟩
    language := "stan1293"
    primaryText := "I'm not sure whether Mary likes any student. Which student does she like?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "doubted"), ("speaker", "same"), ("cleft", "false")] }

def ex58a : Datum :=
  { id := "dayal2016_ex58a"
    source := ⟨"dayal-2016", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm not sure if anyone left the party but I'd like to know who, if anyone, did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "suspended"), ("speaker", "same"), ("cleft", "false")] }

def ex58b : Datum :=
  { id := "dayal2016_ex58b"
    source := ⟨"dayal-2016", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who, if anyone, does Mary like?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "suspended"), ("speaker", "same"), ("cleft", "false")] }

def ex59a : Datum :=
  { id := "dayal2016_ex59a"
    source := ⟨"dayal-2016", "(59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who was it that left the party? No one."
    glossedTokens := []
    context := "No one left the party."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "denied"), ("speaker", "other"), ("cleft", "true")] }

def ex59b : Datum :=
  { id := "dayal2016_ex59b"
    source := ⟨"dayal-2016", "(59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who, if anyone, was it that left the party."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "suspended"), ("speaker", "same"), ("cleft", "true")] }

def ex61a : Datum :=
  { id := "dayal2016_ex61a"
    source := ⟨"dayal-2016", "(61a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who left the party. No one left the party. John knows that no one left the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("phenomenon", "strongExhaustiveness")] }

def ex61b : Datum :=
  { id := "dayal2016_ex61b"
    source := ⟨"dayal-2016", "(61b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No one left so John knows who did."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.4"), ("existence", "denied"), ("speaker", "same"), ("cleft", "false")] }

def ex65a_one : Datum :=
  { id := "dayal2016_ex65a_one"
    source := ⟨"dayal-2016", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which woman did Bill see?"
    glossedTokens := []
    context := "Bill saw Alice but not Betty or Cal."
    judgment := .acceptable
    alternatives := [("Bill saw Alice.", .acceptable), ("Bill saw only Alice.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.4"), ("whNumber", "singular"), ("situation", "one")] }

def ex65a_two : Datum :=
  { id := "dayal2016_ex65a_two"
    source := ⟨"dayal-2016", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which woman did Bill see?"
    glossedTokens := []
    context := "Bill saw Alice and Betty but not Cal."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4"), ("whNumber", "singular"), ("situation", "two")] }

def ex65a_none : Datum :=
  { id := "dayal2016_ex65a_none"
    source := ⟨"dayal-2016", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which woman did Bill see?"
    glossedTokens := []
    context := "Bill saw no one."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4"), ("whNumber", "singular"), ("situation", "none")] }

def ex66a_two : Datum :=
  { id := "dayal2016_ex66a_two"
    source := ⟨"dayal-2016", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which women did Bill see?"
    glossedTokens := []
    context := "Bill saw Alice and Betty but not Cal."
    judgment := .acceptable
    alternatives := [("Bill saw Alice and Betty.", .acceptable), ("Bill saw only Alice and Betty.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.4"), ("whNumber", "plural"), ("situation", "two")] }

def ex66a_one : Datum :=
  { id := "dayal2016_ex66a_one"
    source := ⟨"dayal-2016", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which women did Bill see?"
    glossedTokens := []
    context := "Bill saw Alice but not Betty or Cal."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4"), ("whNumber", "plural"), ("situation", "one")] }

def ex66a_none : Datum :=
  { id := "dayal2016_ex66a_none"
    source := ⟨"dayal-2016", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which women did Bill see?"
    glossedTokens := []
    context := "Bill saw no one."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4"), ("whNumber", "plural"), ("situation", "none")] }

def all : List Datum := [ex33a, ex33b, ex33c, ex34a, ex39a, ex39b, ex41a_42a, ex41a_42b, ex41b_42a, ex41b_42b, ex41c_42a, ex41c_42b, ex47a, ex47b, ex51a_singular, ex51a_plural, ex53a, ex53c, ex54a, ex54b, ex55a, ex55b, ex56a, ex56b, ex57a, ex57b, ex58a, ex58b, ex59a, ex59b, ex61a, ex61b, ex65a_one, ex65a_two, ex65a_none, ex66a_two, ex66a_one, ex66a_none]

end Dayal2016.Examples
