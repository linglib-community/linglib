module

public import Linglib.Data.Examples.Schema

/-!
# `BuccolaCrnic2021` — typed example data

Auto-generated from `Linglib/Data/Examples/BuccolaCrnic2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BuccolaCrnic2021.Examples`.
-/

@[expose] public section

namespace BuccolaCrnic2021.Examples

def ex2a : Datum :=
  { id := "buccolacrnic2021_ex2a"
    source := ⟨"buccola-crnic-2021", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that Mary and any boy have blue eyes"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "distributive"), ("number", "singular")] }

def ex2b : Datum :=
  { id := "buccolacrnic2021_ex2b"
    source := ⟨"buccola-crnic-2021", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink any whisky and the soda"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "distributive"), ("number", "mass")] }

def ex4a : Datum :=
  { id := "buccolacrnic2021_ex4a"
    source := ⟨"buccola-crnic-2021", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that Mary or any boy has blue eyes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "or"), ("predicate", "distributive"), ("number", "singular")] }

def ex4b : Datum :=
  { id := "buccolacrnic2021_ex4b"
    source := ⟨"buccola-crnic-2021", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink any whisky or the soda"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "or"), ("predicate", "distributive"), ("number", "mass")] }

def ex7a : Datum :=
  { id := "buccolacrnic2021_ex7a"
    source := ⟨"buccola-crnic-2021", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think that Mary and any boy here have ever laughed at my jokes"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "distributive"), ("number", "singular")] }

def ex7b : Datum :=
  { id := "buccolacrnic2021_ex7b"
    source := ⟨"buccola-crnic-2021", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think that Mary and any boy here have ever collaborated"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "collective"), ("number", "singular")] }

def ex8a : Datum :=
  { id := "buccolacrnic2021_ex8a"
    source := ⟨"buccola-crnic-2021", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't drink the soda and any whisky"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "distributive"), ("number", "mass")] }

def ex8b : Datum :=
  { id := "buccolacrnic2021_ex8b"
    source := ⟨"buccola-crnic-2021", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't mix the soda and any whisky"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "collective"), ("number", "mass")] }

def ex10a : Datum :=
  { id := "buccolacrnic2021_ex10a"
    source := ⟨"buccola-crnic-2021", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think that Mary and any boy here have ever laughed at each other's jokes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "collective"), ("number", "singular")] }

def ex10b : Datum :=
  { id := "buccolacrnic2021_ex10b"
    source := ⟨"buccola-crnic-2021", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The zookeeper didn't put any monkey and the lion into the same cage"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "collective"), ("number", "singular")] }

def ex10c : Datum :=
  { id := "buccolacrnic2021_ex10c"
    source := ⟨"buccola-crnic-2021", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John denies that Mary and any student of hers have ever written a paper together"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "collective"), ("number", "singular")] }

def ex26 : Datum :=
  { id := "buccolacrnic2021_ex26"
    source := ⟨"buccola-crnic-2021", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think that the girls and any boys have blue eyes"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "distributive"), ("number", "plural")] }

def ex29 : Datum :=
  { id := "buccolacrnic2021_ex29"
    source := ⟨"buccola-crnic-2021", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think that the girls and any boys have ever written a paper together"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coordination", "and"), ("predicate", "collective"), ("number", "plural")] }

def ex32a : Datum :=
  { id := "buccolacrnic2021_ex32a"
    source := ⟨"buccola-crnic-2021", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have one colleague who has read any paper of mine"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("numeral", "one"), ("predicate", "distributive")] }

def ex32b : Datum :=
  { id := "buccolacrnic2021_ex32b"
    source := ⟨"buccola-crnic-2021", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have four colleagues who have read any paper of mine"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("numeral", "four"), ("predicate", "distributive")] }

def ex32c : Datum :=
  { id := "buccolacrnic2021_ex32c"
    source := ⟨"buccola-crnic-2021", "(32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have four colleagues who have written any paper together"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("numeral", "four"), ("predicate", "collective")] }

def ex37a : Datum :=
  { id := "buccolacrnic2021_ex37a"
    source := ⟨"buccola-crnic-2021", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not all students did any homework"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "all")] }

def ex37b : Datum :=
  { id := "buccolacrnic2021_ex37b"
    source := ⟨"buccola-crnic-2021", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't always read any books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "always")] }

def all : List Datum := [ex2a, ex2b, ex4a, ex4b, ex7a, ex7b, ex8a, ex8b, ex10a, ex10b, ex10c, ex26, ex29, ex32a, ex32b, ex32c, ex37a, ex37b]

end BuccolaCrnic2021.Examples
