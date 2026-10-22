module

public import Linglib.Data.Examples.Schema

/-!
# `Erlewine2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Erlewine2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Erlewine2020.Examples`.
-/

@[expose] public section

namespace Erlewine2020.Examples

def ex6a : Datum :=
  { id := "erlewine2020_ex6a"
    source := ⟨"erlewine-2020", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did he say hid the rutabaga?"
    glossedTokens := []
    context := "Long-distance subject extraction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "none")] }

def ex6a_that : Datum :=
  { id := "erlewine2020_ex6a_that"
    source := ⟨"erlewine-2020", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did he say that hid the rutabaga?"
    glossedTokens := []
    context := "Long-distance subject extraction across that."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex6b : Datum :=
  { id := "erlewine2020_ex6b"
    source := ⟨"erlewine-2020", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did he say Laura hid?"
    glossedTokens := []
    context := "Long-distance object extraction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "none")] }

def ex6b_that : Datum :=
  { id := "erlewine2020_ex6b_that"
    source := ⟨"erlewine-2020", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did he say that Laura hid?"
    glossedTokens := []
    context := "Long-distance object extraction across that."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex12a : Datum :=
  { id := "erlewine2020_ex12a"
    source := ⟨"erlewine-2020", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What do you think that is in the box?"
    glossedTokens := []
    context := "The subject extracted from Spec,TP across that."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex12b : Datum :=
  { id := "erlewine2020_ex12b"
    source := ⟨"erlewine-2020", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What do you think that there is in the box?"
    glossedTokens := []
    context := "The subject extracted from the small clause, there in Spec,TP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex13a : Datum :=
  { id := "erlewine2020_ex13a"
    source := ⟨"erlewine-2020", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did she say that tomorrow would regret his words?"
    glossedTokens := []
    context := "A high adverb between that and the subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex13a_noadverb : Datum :=
  { id := "erlewine2020_ex13a_noadverb"
    source := ⟨"erlewine-2020", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did she say that would regret his words?"
    glossedTokens := []
    context := "No adverb between that and the subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex15a : Datum :=
  { id := "erlewine2020_ex15a"
    source := ⟨"erlewine-2020", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did John say that fortunately ran to the store?"
    glossedTokens := []
    context := "A high adverb above TP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex15b : Datum :=
  { id := "erlewine2020_ex15b"
    source := ⟨"erlewine-2020", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did John say that quickly ran to the store?"
    glossedTokens := []
    context := "A low adverb below TP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex18a : Datum :=
  { id := "erlewine2020_ex18a"
    source := ⟨"erlewine-2020", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's in these villages that we all believe can be found the best examples of this cuisine."
    glossedTokens := []
    context := "The locative of locative inversion extracted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "none")] }

def ex18a_that : Datum :=
  { id := "erlewine2020_ex18a_that"
    source := ⟨"erlewine-2020", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's in these villages that we all believe that can be found the best examples of this cuisine."
    glossedTokens := []
    context := "The locative of locative inversion extracted across that."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def ex18b : Datum :=
  { id := "erlewine2020_ex18b"
    source := ⟨"erlewine-2020", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's in these villages that we all believe the best examples of this cuisine can be found."
    glossedTokens := []
    context := "The locative extracted without locative inversion."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "none")] }

def ex18b_that : Datum :=
  { id := "erlewine2020_ex18b_that"
    source := ⟨"erlewine-2020", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's in these villages that we all believe that the best examples of this cuisine can be found."
    glossedTokens := []
    context := "The locative extracted across that without locative inversion."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complementizer", "that")] }

def all : List Datum := [ex6a, ex6a_that, ex6b, ex6b_that, ex12a, ex12b, ex13a, ex13a_noadverb, ex15a, ex15b, ex18a, ex18a_that, ex18b, ex18b_that]

end Erlewine2020.Examples
