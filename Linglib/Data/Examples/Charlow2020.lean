module

public import Linglib.Data.Examples.Schema

/-!
# `Charlow2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Charlow2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Charlow2020.Examples`.
-/

@[expose] public section

namespace Charlow2020.Examples

def ex1 : Datum :=
  { id := "charlow2020_ex1"
    source := ⟨"charlow-2020", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a rich relative of mine dies, I'll inherit a house."
    glossedTokens := []
    context := "The speaker has exactly one rich relative who has put the speaker in her will, though the speaker may not know who she is."
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > if", .acceptable)]
    paperFeatures := [] }

def ex2 : Datum :=
  { id := "charlow2020_ex2"
    source := ⟨"charlow-2020", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If every rich relative of mine dies, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∀ > if", .unacceptable)]
    paperFeatures := [] }

def ex3 : Datum :=
  { id := "charlow2020_ex3"
    source := ⟨"charlow-2020", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each student has to come up with three arguments showing that some condition proposed by Chomsky is wrong."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∀ > ∃ > 3", .acceptable)]
    paperFeatures := [] }

def ex39 : Datum :=
  { id := "charlow2020_ex39"
    source := ⟨"charlow-2020", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If two relatives of mine die, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("2 > if, both deaths in the antecedent", .acceptable), ("2 > each > if", .unacceptable)]
    paperFeatures := [] }

def ex43 : Datum :=
  { id := "charlow2020_ex43"
    source := ⟨"charlow-2020", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a persuasive lawyer visits a rich relative of mine, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃lawyer > if > ∃relative", .acceptable), ("∃relative > if > ∃lawyer", .acceptable), ("∃relative > ∃lawyer > if", .acceptable)]
    paperFeatures := [] }

def ex46 : Datum :=
  { id := "charlow2020_ex46"
    source := ⟨"charlow-2020", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each student has to come up with three arguments showing that some condition proposed by a famous syntactician is wrong."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃syntactician > ∀ > ∃condition > 3", .acceptable)]
    paperFeatures := [] }

def ex47 : Datum :=
  { id := "charlow2020_ex47"
    source := ⟨"charlow-2020", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every grad would be overjoyed if some paper on indefinites was discussed in a popular grad seminar being offered this term."
    glossedTokens := []
    context := "Every grad is taking the semantics seminar, and the grads like different papers on indefinites."
    judgment := .acceptable
    contrasts := []
    readings := [("∃seminar > ∀ > ∃paper > if", .acceptable)]
    paperFeatures := [] }

def ex51 : Datum :=
  { id := "charlow2020_ex51"
    source := ⟨"charlow-2020", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody loves it when a famous expert on indefinites cites him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > ∀, pronoun bound by everybody", .acceptable)]
    paperFeatures := [] }

def ex52 : Datum :=
  { id := "charlow2020_ex52"
    source := ⟨"brasoveanu-farkas-2011", "(49)"⟩
    reportedIn := some ⟨"charlow-2020", "(52)"⟩
    language := "stan1293"
    primaryText := "Every boy who talked to a friend of his left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > ∀, pronoun bound by every boy", .unacceptable)]
    paperFeatures := [] }

def ex53 : Datum :=
  { id := "charlow2020_ex53"
    source := ⟨"charlow-2020", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No candidate submitted a paper he had written."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > no, pronoun bound by no candidate", .unacceptable)]
    paperFeatures := [] }

def all : List Datum := [ex1, ex2, ex3, ex39, ex43, ex46, ex47, ex51, ex52, ex53]

end Charlow2020.Examples
