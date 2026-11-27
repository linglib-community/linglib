module

public import Linglib.Data.Examples.Schema
public import Mathlib.Tactic.DeriveFintype

/-!
# `TheilerEtAl2019` — typed example data

Auto-generated from `Linglib/Data/Examples/TheilerEtAl2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TheilerEtAl2019.Examples`.
-/

@[expose] public section

namespace TheilerEtAl2019.Examples

def ex_1_that : Datum :=
  { id := "theileretal2019_1_that"
    source := ⟨"theiler-etal-2019", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill knows that Mary has eaten."
    glossedTokens := [("Bill", ""), ("knows", ""), ("that", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['k', 'n', 'o', 'w', 's'], [], [⟨['k', 'n', 'o', 'w', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "know"⟩, ⟨2, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_1_whether : Datum :=
  { id := "theileretal2019_1_whether"
    source := ⟨"theiler-etal-2019", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill knows whether Mary has eaten."
    glossedTokens := [("Bill", ""), ("knows", ""), ("whether", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['k', 'n', 'o', 'w', 's'], [], [⟨['k', 'n', 'o', 'w', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "know"⟩, ⟨2, 1, "complementizer", some "whether"⟩]
    paperFeatures := [] }

def ex_1_what : Datum :=
  { id := "theileretal2019_1_what"
    source := ⟨"theiler-etal-2019", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill knows what Mary has eaten."
    glossedTokens := [("Bill", ""), ("knows", ""), ("what", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['k', 'n', 'o', 'w', 's'], [], [⟨['k', 'n', 'o', 'w', 's'], [], none⟩]⟩, ⟨['w', 'h', 'a', 't'], [], [⟨['w', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "know"⟩, ⟨2, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_2_that : Datum :=
  { id := "theileretal2019_2_that"
    source := ⟨"theiler-etal-2019", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill believes that Mary has eaten."
    glossedTokens := [("Bill", ""), ("believes", ""), ("that", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], [⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "believe"⟩, ⟨2, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_2_whether : Datum :=
  { id := "theileretal2019_2_whether"
    source := ⟨"theiler-etal-2019", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill believes whether Mary has eaten."
    glossedTokens := [("Bill", ""), ("believes", ""), ("whether", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], [⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "believe"⟩, ⟨2, 1, "complementizer", some "whether"⟩]
    paperFeatures := [] }

def ex_2_what : Datum :=
  { id := "theileretal2019_2_what"
    source := ⟨"theiler-etal-2019", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill believes what Mary has eaten."
    glossedTokens := [("Bill", ""), ("believes", ""), ("what", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], [⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'a', 't'], [], [⟨['w', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "believe"⟩, ⟨2, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_3_whether : Datum :=
  { id := "theileretal2019_3_whether"
    source := ⟨"theiler-etal-2019", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wonders whether Mary has eaten."
    glossedTokens := [("Bill", ""), ("wonders", ""), ("whether", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], [⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "wonder"⟩, ⟨2, 1, "complementizer", some "whether"⟩]
    paperFeatures := [] }

def ex_3_what : Datum :=
  { id := "theileretal2019_3_what"
    source := ⟨"theiler-etal-2019", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wonders what Mary has eaten."
    glossedTokens := [("Bill", ""), ("wonders", ""), ("what", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], [⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], none⟩]⟩, ⟨['w', 'h', 'a', 't'], [], [⟨['w', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "wonder"⟩, ⟨2, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_3_that : Datum :=
  { id := "theileretal2019_3_that"
    source := ⟨"theiler-etal-2019", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wonders that Mary has eaten."
    glossedTokens := [("Bill", ""), ("wonders", ""), ("that", ""), ("Mary", ""), ("has", ""), ("eaten", "")]
    glossedWords := [⟨['B', 'i', 'l', 'l'], [], [⟨['B', 'i', 'l', 'l'], [], none⟩]⟩, ⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], [⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['e', 'a', 't', 'e', 'n'], [], [⟨['e', 'a', 't', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "wonder"⟩, ⟨2, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_8 : Datum :=
  { id := "theileretal2019_8"
    source := ⟨"theiler-etal-2019", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is certain that John left."
    glossedTokens := [("Mary", ""), ("is", ""), ("certain", ""), ("that", ""), ("John", ""), ("left", "")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], [⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "beCertain"⟩, ⟨3, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_9 : Datum :=
  { id := "theileretal2019_9"
    source := ⟨"theiler-etal-2019", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is certain who left."
    glossedTokens := [("Mary", ""), ("is", ""), ("certain", ""), ("who", ""), ("left", "")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], [⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], none⟩]⟩, ⟨['w', 'h', 'o'], [], [⟨['w', 'h', 'o'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "beCertain"⟩, ⟨3, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_15 : Datum :=
  { id := "theileretal2019_15"
    source := ⟨"theiler-etal-2019", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't believe that Ann left."
    glossedTokens := [("Mary", ""), ("doesn't", ""), ("believe", ""), ("that", ""), ("Ann", ""), ("left", "")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], [⟨['d', 'o', 'e', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['b', 'e', 'l', 'i', 'e', 'v', 'e'], [], [⟨['b', 'e', 'l', 'i', 'e', 'v', 'e'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['A', 'n', 'n'], [], [⟨['A', 'n', 'n'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("lowered", .acceptable)]
    spans := [⟨2, 1, "predicate", some "believe"⟩, ⟨3, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_31 : Datum :=
  { id := "theileretal2019_31"
    source := ⟨"theiler-etal-2019", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes whether Mary left."
    glossedTokens := [("John", ""), ("believes", ""), ("whether", ""), ("Mary", ""), ("left", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], [⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "believe"⟩, ⟨2, 1, "complementizer", some "whether"⟩]
    paperFeatures := [] }

def ex_38 : Datum :=
  { id := "theileretal2019_38"
    source := ⟨"theiler-etal-2019", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders that Mary called."
    glossedTokens := [("John", ""), ("wonders", ""), ("that", ""), ("Mary", ""), ("called", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], [⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['c', 'a', 'l', 'l', 'e', 'd'], [], [⟨['c', 'a', 'l', 'l', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "wonder"⟩, ⟨2, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_40 : Datum :=
  { id := "theileretal2019_40"
    source := ⟨"theiler-etal-2019", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whether the light is on depends on whether the switch is up."
    glossedTokens := [("Whether", ""), ("the", ""), ("light", ""), ("is", ""), ("on", ""), ("depends", ""), ("on", ""), ("whether", ""), ("the", ""), ("switch", ""), ("is", ""), ("up", "")]
    glossedWords := [⟨['W', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['W', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'i', 'g', 'h', 't'], [], [⟨['l', 'i', 'g', 'h', 't'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['d', 'e', 'p', 'e', 'n', 'd', 's'], [], [⟨['d', 'e', 'p', 'e', 'n', 'd', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'w', 'i', 't', 'c', 'h'], [], [⟨['s', 'w', 'i', 't', 'c', 'h'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 2, "predicate", some "dependOn"⟩, ⟨0, 1, "subjectComplementizer", some "whether"⟩, ⟨7, 1, "complementizer", some "whether"⟩]
    paperFeatures := [] }

def ex_42 : Datum :=
  { id := "theileretal2019_42"
    source := ⟨"theiler-etal-2019", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That the light is on depends on whether the switch is up."
    glossedTokens := [("That", ""), ("the", ""), ("light", ""), ("is", ""), ("on", ""), ("depends", ""), ("on", ""), ("whether", ""), ("the", ""), ("switch", ""), ("is", ""), ("up", "")]
    glossedWords := [⟨['T', 'h', 'a', 't'], [], [⟨['T', 'h', 'a', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'i', 'g', 'h', 't'], [], [⟨['l', 'i', 'g', 'h', 't'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['d', 'e', 'p', 'e', 'n', 'd', 's'], [], [⟨['d', 'e', 'p', 'e', 'n', 'd', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['w', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'w', 'i', 't', 'c', 'h'], [], [⟨['s', 'w', 'i', 't', 'c', 'h'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨5, 2, "predicate", some "dependOn"⟩, ⟨0, 1, "subjectComplementizer", some "that"⟩, ⟨7, 1, "complementizer", some "whether"⟩]
    paperFeatures := [] }

def ex_43 : Datum :=
  { id := "theileretal2019_43"
    source := ⟨"theiler-etal-2019", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whether the light is on depends on that the switch is up."
    glossedTokens := [("Whether", ""), ("the", ""), ("light", ""), ("is", ""), ("on", ""), ("depends", ""), ("on", ""), ("that", ""), ("the", ""), ("switch", ""), ("is", ""), ("up", "")]
    glossedWords := [⟨['W', 'h', 'e', 't', 'h', 'e', 'r'], [], [⟨['W', 'h', 'e', 't', 'h', 'e', 'r'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['l', 'i', 'g', 'h', 't'], [], [⟨['l', 'i', 'g', 'h', 't'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['d', 'e', 'p', 'e', 'n', 'd', 's'], [], [⟨['d', 'e', 'p', 'e', 'n', 'd', 's'], [], none⟩]⟩, ⟨['o', 'n'], [], [⟨['o', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'w', 'i', 't', 'c', 'h'], [], [⟨['s', 'w', 'i', 't', 'c', 'h'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['u', 'p'], [], [⟨['u', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨5, 2, "predicate", some "dependOn"⟩, ⟨0, 1, "subjectComplementizer", some "whether"⟩, ⟨7, 1, "complementizer", some "that"⟩]
    paperFeatures := [] }

def ex_44a_believe : Datum :=
  { id := "theileretal2019_44a_believe"
    source := ⟨"theiler-etal-2019", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that Mary left and when she did."
    glossedTokens := [("John", ""), ("believes", ""), ("that", ""), ("Mary", ""), ("left", ""), ("and", ""), ("when", ""), ("she", ""), ("did", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], [⟨['b', 'e', 'l', 'i', 'e', 'v', 'e', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'n'], [], [⟨['w', 'h', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'i', 'd'], [], [⟨['d', 'i', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "believe"⟩, ⟨2, 1, "complementizer", some "that"⟩, ⟨6, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_44a_think : Datum :=
  { id := "theileretal2019_44a_think"
    source := ⟨"theiler-etal-2019", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks that Mary left and when she did."
    glossedTokens := [("John", ""), ("thinks", ""), ("that", ""), ("Mary", ""), ("left", ""), ("and", ""), ("when", ""), ("she", ""), ("did", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['t', 'h', 'i', 'n', 'k', 's'], [], [⟨['t', 'h', 'i', 'n', 'k', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'n'], [], [⟨['w', 'h', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'i', 'd'], [], [⟨['d', 'i', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "think"⟩, ⟨2, 1, "complementizer", some "that"⟩, ⟨6, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_44b : Datum :=
  { id := "theileretal2019_44b"
    source := ⟨"theiler-etal-2019", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is true that Mary left and when she did."
    glossedTokens := [("It", ""), ("is", ""), ("true", ""), ("that", ""), ("Mary", ""), ("left", ""), ("and", ""), ("when", ""), ("she", ""), ("did", "")]
    glossedWords := [⟨['I', 't'], [], [⟨['I', 't'], [], none⟩]⟩, ⟨['i', 's'], [], [⟨['i', 's'], [], none⟩]⟩, ⟨['t', 'r', 'u', 'e'], [], [⟨['t', 'r', 'u', 'e'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'n'], [], [⟨['w', 'h', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'i', 'd'], [], [⟨['d', 'i', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 1, "predicate", some "beTrue"⟩, ⟨3, 1, "complementizer", some "that"⟩, ⟨7, 1, "wh", none⟩]
    paperFeatures := [] }

def ex_44c : Datum :=
  { id := "theileretal2019_44c"
    source := ⟨"theiler-etal-2019", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders that Mary left and when she did."
    glossedTokens := [("John", ""), ("wonders", ""), ("that", ""), ("Mary", ""), ("left", ""), ("and", ""), ("when", ""), ("she", ""), ("did", "")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], [], [⟨['J', 'o', 'h', 'n'], [], none⟩]⟩, ⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], [⟨['w', 'o', 'n', 'd', 'e', 'r', 's'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], [], [⟨['M', 'a', 'r', 'y'], [], none⟩]⟩, ⟨['l', 'e', 'f', 't'], [], [⟨['l', 'e', 'f', 't'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['w', 'h', 'e', 'n'], [], [⟨['w', 'h', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'h', 'e'], [], [⟨['s', 'h', 'e'], [], none⟩]⟩, ⟨['d', 'i', 'd'], [], [⟨['d', 'i', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "predicate", some "wonder"⟩, ⟨2, 1, "complementizer", some "that"⟩, ⟨6, 1, "wh", none⟩]
    paperFeatures := [] }

def all : List Datum := [ex_1_that, ex_1_whether, ex_1_what, ex_2_that, ex_2_whether, ex_2_what, ex_3_whether, ex_3_what, ex_3_that, ex_8, ex_9, ex_15, ex_31, ex_38, ex_40, ex_42, ex_43, ex_44a_believe, ex_44a_think, ex_44b, ex_44c]

/-- The readings of a negated neg-raising predicate. -/
inductive Reading where
  /-- lowered: the negation is understood in the complement -/
  | lowered
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .lowered => "lowered"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- predicate: the clause-embedding predicate under test -/
  | predicate
  /-- complementizer: the complementizer of a complement clause -/
  | complementizer
  /-- wh: the interrogative phrase of a complement clause -/
  | wh
  /-- subjectComplementizer: the complementizer of a clausal subject -/
  | subjectComplementizer
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("predicate", .predicate), ("complementizer", .complementizer), ("wh", .wh), ("subjectComplementizer", .subjectComplementizer)]

/-- The predicates under test and the complementizers of their clauses. -/
inductive Lexeme where
  /-- know: English *know* -/
  | know
  /-- believe: English *believe* -/
  | believe
  /-- think: English *think* -/
  | think
  /-- wonder: English *wonder* -/
  | wonder
  /-- dependOn: English *depend on* -/
  | dependOn
  /-- beCertain: English *be certain* -/
  | beCertain
  /-- beTrue: English *be true* -/
  | beTrue
  /-- that: English *that* -/
  | that
  /-- whether: English *whether* -/
  | whether
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("know", .know), ("believe", .believe), ("think", .think), ("wonder", .wonder), ("dependOn", .dependOn), ("beCertain", .beCertain), ("beTrue", .beTrue), ("that", .that), ("whether", .whether)])

/-- The judged sentences of the article with a clause-embedding predicate under test. -/
inductive Example where
  | ex_1_that
  | ex_1_whether
  | ex_1_what
  | ex_2_that
  | ex_2_whether
  | ex_2_what
  | ex_3_whether
  | ex_3_what
  | ex_3_that
  | ex_8
  | ex_9
  | ex_15
  | ex_31
  | ex_38
  | ex_40
  | ex_42
  | ex_43
  | ex_44a_believe
  | ex_44a_think
  | ex_44b
  | ex_44c
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_1_that, .ex_1_whether, .ex_1_what, .ex_2_that, .ex_2_whether, .ex_2_what, .ex_3_whether,
    .ex_3_what, .ex_3_that, .ex_8, .ex_9, .ex_15, .ex_31, .ex_38, .ex_40, .ex_42, .ex_43,
    .ex_44a_believe, .ex_44a_think, .ex_44b, .ex_44c]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_1_that => _root_.TheilerEtAl2019.Examples.ex_1_that
  | .ex_1_whether => _root_.TheilerEtAl2019.Examples.ex_1_whether
  | .ex_1_what => _root_.TheilerEtAl2019.Examples.ex_1_what
  | .ex_2_that => _root_.TheilerEtAl2019.Examples.ex_2_that
  | .ex_2_whether => _root_.TheilerEtAl2019.Examples.ex_2_whether
  | .ex_2_what => _root_.TheilerEtAl2019.Examples.ex_2_what
  | .ex_3_whether => _root_.TheilerEtAl2019.Examples.ex_3_whether
  | .ex_3_what => _root_.TheilerEtAl2019.Examples.ex_3_what
  | .ex_3_that => _root_.TheilerEtAl2019.Examples.ex_3_that
  | .ex_8 => _root_.TheilerEtAl2019.Examples.ex_8
  | .ex_9 => _root_.TheilerEtAl2019.Examples.ex_9
  | .ex_15 => _root_.TheilerEtAl2019.Examples.ex_15
  | .ex_31 => _root_.TheilerEtAl2019.Examples.ex_31
  | .ex_38 => _root_.TheilerEtAl2019.Examples.ex_38
  | .ex_40 => _root_.TheilerEtAl2019.Examples.ex_40
  | .ex_42 => _root_.TheilerEtAl2019.Examples.ex_42
  | .ex_43 => _root_.TheilerEtAl2019.Examples.ex_43
  | .ex_44a_believe => _root_.TheilerEtAl2019.Examples.ex_44a_believe
  | .ex_44a_think => _root_.TheilerEtAl2019.Examples.ex_44a_think
  | .ex_44b => _root_.TheilerEtAl2019.Examples.ex_44b
  | .ex_44c => _root_.TheilerEtAl2019.Examples.ex_44c

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.TheilerEtAl2019.Examples.all := rfl

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_1_that => [(.predicate, .know), (.complementizer, .that)]
  | .ex_1_whether => [(.predicate, .know), (.complementizer, .whether)]
  | .ex_1_what => [(.predicate, .know)]
  | .ex_2_that => [(.predicate, .believe), (.complementizer, .that)]
  | .ex_2_whether => [(.predicate, .believe), (.complementizer, .whether)]
  | .ex_2_what => [(.predicate, .believe)]
  | .ex_3_whether => [(.predicate, .wonder), (.complementizer, .whether)]
  | .ex_3_what => [(.predicate, .wonder)]
  | .ex_3_that => [(.predicate, .wonder), (.complementizer, .that)]
  | .ex_8 => [(.predicate, .beCertain), (.complementizer, .that)]
  | .ex_9 => [(.predicate, .beCertain)]
  | .ex_15 => [(.predicate, .believe), (.complementizer, .that)]
  | .ex_31 => [(.predicate, .believe), (.complementizer, .whether)]
  | .ex_38 => [(.predicate, .wonder), (.complementizer, .that)]
  | .ex_40 => [(.predicate, .dependOn), (.subjectComplementizer, .whether), (.complementizer, .whether)]
  | .ex_42 => [(.predicate, .dependOn), (.subjectComplementizer, .that), (.complementizer, .whether)]
  | .ex_43 => [(.predicate, .dependOn), (.subjectComplementizer, .whether), (.complementizer, .that)]
  | .ex_44a_believe => [(.predicate, .believe), (.complementizer, .that)]
  | .ex_44a_think => [(.predicate, .think), (.complementizer, .that)]
  | .ex_44b => [(.predicate, .beTrue), (.complementizer, .that)]
  | .ex_44c => [(.predicate, .wonder), (.complementizer, .that)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.TheilerEtAl2019.Examples.label? · = some l)).filterMap _root_.TheilerEtAl2019.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

/-- The readings the example judges, each with its judgment. -/
def Example.readings : Example → List (Reading × Judgment)
  | .ex_1_that => []
  | .ex_1_whether => []
  | .ex_1_what => []
  | .ex_2_that => []
  | .ex_2_whether => []
  | .ex_2_what => []
  | .ex_3_whether => []
  | .ex_3_what => []
  | .ex_3_that => []
  | .ex_8 => []
  | .ex_9 => []
  | .ex_15 => [(.lowered, .acceptable)]
  | .ex_31 => []
  | .ex_38 => []
  | .ex_40 => []
  | .ex_42 => []
  | .ex_43 => []
  | .ex_44a_believe => []
  | .ex_44a_think => []
  | .ex_44b => []
  | .ex_44c => []

/-- The judgment the example records for the reading, if it records one. -/
def Example.reading (x : Example) (r : Reading) : Option Judgment :=
  (x.readings.lookup r)

theorem Example.reading_datum : ∀ (x : Example) (r : Reading),
    _root_.TheilerEtAl2019.Examples.reading x.datum r = x.reading r := by
  decide +kernel

end TheilerEtAl2019.Examples
