module

public import Linglib.Data.Examples.Schema

/-!
# `UegakiSudo2019` — typed example data

Auto-generated from `Linglib/Data/Examples/UegakiSudo2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace UegakiSudo2019.Examples`.
-/

@[expose] public section

namespace UegakiSudo2019.Examples

def ex_6a : Datum :=
  { id := "uegakisudo2019_6a"
    source := ⟨"uegaki-sudo-2019", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben hopes/wishes that Becky is invited to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "non-veridical preferential"), ("complement", "declarative")] }

def ex_6c : Datum :=
  { id := "uegakisudo2019_6c"
    source := ⟨"uegaki-sudo-2019", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dorothy is surprised/annoyed/glad/happy that Daniel will give a presentation."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "declarative")] }

def ex_7b : Datum :=
  { id := "uegakisudo2019_7b"
    source := ⟨"uegaki-sudo-2019", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben is happy/glad ?(about) which students are invited to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "wh-interrogative")] }

def ex_7c : Datum :=
  { id := "uegakisudo2019_7c"
    source := ⟨"uegaki-sudo-2019", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris liked/hated which students were invited to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "wh-interrogative")] }

def ex_8a : Datum :=
  { id := "uegakisudo2019_8a"
    source := ⟨"uegaki-sudo-2019", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben hopes/wishes which students will be invited to the party."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "non-veridical preferential"), ("complement", "wh-interrogative")] }

def ex_8b : Datum :=
  { id := "uegakisudo2019_8b"
    source := ⟨"uegaki-sudo-2019", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris expects/fears how many students will be invited to the party."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "non-veridical preferential"), ("complement", "wh-interrogative")] }

def ex_10b : Datum :=
  { id := "uegakisudo2019_10b"
    source := ⟨"uegaki-sudo-2019", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ben is glad/happy (about) whether Becky is invited to the party."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "whether-interrogative")] }

def ex_40a : Datum :=
  { id := "uegakisudo2019_40a"
    source := ⟨"uegaki-sudo-2019", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is happy that ALICE jumped."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John's preference for Alice's jumping is compared to alternatives false at the evaluation world", .acceptable)]
    paperFeatures := [("predicate", "veridical preferential"), ("focus", "subject")] }

def ex_40b : Datum :=
  { id := "uegakisudo2019_40b"
    source := ⟨"uegaki-sudo-2019", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hopes that ALICE jumped."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John's preference for Alice's jumping is compared only to alternatives he considers possible", .acceptable)]
    paperFeatures := [("predicate", "non-veridical preferential"), ("focus", "subject")] }

def ex_41 : Datum :=
  { id := "uegakisudo2019_41"
    source := ⟨"uegaki-sudo-2019", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't happy about / doesn't like which student will sing."
    glossedTokens := []
    context := "There is no particular student John wants to sing. John knows which student will sing."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "veridical preferential"), ("complement", "wh-interrogative"), ("evidence", "Threshold Significance")] }

def ex_42 : Datum :=
  { id := "uegakisudo2019_42"
    source := ⟨"uegaki-sudo-2019", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is indifferent about which student will sing."
    glossedTokens := []
    context := "There is no particular student John wants to sing."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "be indifferent"), ("complement", "wh-interrogative")] }

def ex_43a : Datum :=
  { id := "uegakisudo2019_43a"
    source := ⟨"uegaki-sudo-2019", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is indifferent that Alice will sing."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("predicate", "be indifferent"), ("complement", "declarative")] }

def all : List Datum := [ex_6a, ex_6c, ex_7b, ex_7c, ex_8a, ex_8b, ex_10b, ex_40a, ex_40b, ex_41, ex_42, ex_43a]

end UegakiSudo2019.Examples
