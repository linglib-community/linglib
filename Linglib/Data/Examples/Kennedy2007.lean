module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Kennedy2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Kennedy2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kennedy2007.Examples`.
-/

@[expose] public section

namespace Kennedy2007.Examples

def ex_62a_perfectly_tall : Datum :=
  { id := "kennedy2007_62a_perfectly_tall"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly tall"
    glossedTokens := [("perfectly", ""), ("tall", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['t', 'a', 'l', 'l'], [], [⟨['t', 'a', 'l', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "tall"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62a_slightly_tall : Datum :=
  { id := "kennedy2007_62a_slightly_tall"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly tall"
    glossedTokens := [("slightly", ""), ("tall", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['t', 'a', 'l', 'l'], [], [⟨['t', 'a', 'l', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "tall"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62a_perfectly_deep : Datum :=
  { id := "kennedy2007_62a_perfectly_deep"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly deep"
    glossedTokens := [("perfectly", ""), ("deep", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['d', 'e', 'e', 'p'], [], [⟨['d', 'e', 'e', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "deep"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62a_slightly_deep : Datum :=
  { id := "kennedy2007_62a_slightly_deep"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly deep"
    glossedTokens := [("slightly", ""), ("deep", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['d', 'e', 'e', 'p'], [], [⟨['d', 'e', 'e', 'p'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "deep"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62a_perfectly_expensive : Datum :=
  { id := "kennedy2007_62a_perfectly_expensive"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly expensive"
    glossedTokens := [("perfectly", ""), ("expensive", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], [⟨['e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "expensive"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62a_slightly_expensive : Datum :=
  { id := "kennedy2007_62a_slightly_expensive"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly expensive"
    glossedTokens := [("slightly", ""), ("expensive", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], [⟨['e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "expensive"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62a_perfectly_likely : Datum :=
  { id := "kennedy2007_62a_perfectly_likely"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly likely"
    glossedTokens := [("perfectly", ""), ("likely", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['l', 'i', 'k', 'e', 'l', 'y'], [], [⟨['l', 'i', 'k', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62a_slightly_likely : Datum :=
  { id := "kennedy2007_62a_slightly_likely"
    source := ⟨"kennedy-2007", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly likely"
    glossedTokens := [("slightly", ""), ("likely", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['l', 'i', 'k', 'e', 'l', 'y'], [], [⟨['l', 'i', 'k', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62b_perfectly_short : Datum :=
  { id := "kennedy2007_62b_perfectly_short"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly short"
    glossedTokens := [("perfectly", ""), ("short", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'h', 'o', 'r', 't'], [], [⟨['s', 'h', 'o', 'r', 't'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "short"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62b_slightly_short : Datum :=
  { id := "kennedy2007_62b_slightly_short"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly short"
    glossedTokens := [("slightly", ""), ("short", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'h', 'o', 'r', 't'], [], [⟨['s', 'h', 'o', 'r', 't'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "short"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62b_perfectly_shallow : Datum :=
  { id := "kennedy2007_62b_perfectly_shallow"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly shallow"
    glossedTokens := [("perfectly", ""), ("shallow", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'l', 'l', 'o', 'w'], [], [⟨['s', 'h', 'a', 'l', 'l', 'o', 'w'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "shallow"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62b_slightly_shallow : Datum :=
  { id := "kennedy2007_62b_slightly_shallow"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly shallow"
    glossedTokens := [("slightly", ""), ("shallow", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'h', 'a', 'l', 'l', 'o', 'w'], [], [⟨['s', 'h', 'a', 'l', 'l', 'o', 'w'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "shallow"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62b_perfectly_inexpensive : Datum :=
  { id := "kennedy2007_62b_perfectly_inexpensive"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly inexpensive"
    glossedTokens := [("perfectly", ""), ("inexpensive", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['i', 'n', 'e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], [⟨['i', 'n', 'e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62b_slightly_inexpensive : Datum :=
  { id := "kennedy2007_62b_slightly_inexpensive"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly inexpensive"
    glossedTokens := [("slightly", ""), ("inexpensive", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['i', 'n', 'e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], [⟨['i', 'n', 'e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_62b_perfectly_unlikely : Datum :=
  { id := "kennedy2007_62b_perfectly_unlikely"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly unlikely"
    glossedTokens := [("perfectly", ""), ("unlikely", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['u', 'n', 'l', 'i', 'k', 'e', 'l', 'y'], [], [⟨['u', 'n', 'l', 'i', 'k', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_62b_slightly_unlikely : Datum :=
  { id := "kennedy2007_62b_slightly_unlikely"
    source := ⟨"kennedy-2007", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly unlikely"
    glossedTokens := [("slightly", ""), ("unlikely", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['u', 'n', 'l', 'i', 'k', 'e', 'l', 'y'], [], [⟨['u', 'n', 'l', 'i', 'k', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63a_perfectly_bent : Datum :=
  { id := "kennedy2007_63a_perfectly_bent"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly bent"
    glossedTokens := [("perfectly", ""), ("bent", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['b', 'e', 'n', 't'], [], [⟨['b', 'e', 'n', 't'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "bent"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63a_slightly_bent : Datum :=
  { id := "kennedy2007_63a_slightly_bent"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly bent"
    glossedTokens := [("slightly", ""), ("bent", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['b', 'e', 'n', 't'], [], [⟨['b', 'e', 'n', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "bent"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63a_perfectly_bumpy : Datum :=
  { id := "kennedy2007_63a_perfectly_bumpy"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly bumpy"
    glossedTokens := [("perfectly", ""), ("bumpy", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['b', 'u', 'm', 'p', 'y'], [], [⟨['b', 'u', 'm', 'p', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63a_slightly_bumpy : Datum :=
  { id := "kennedy2007_63a_slightly_bumpy"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly bumpy"
    glossedTokens := [("slightly", ""), ("bumpy", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['b', 'u', 'm', 'p', 'y'], [], [⟨['b', 'u', 'm', 'p', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63a_perfectly_dirty : Datum :=
  { id := "kennedy2007_63a_perfectly_dirty"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly dirty"
    glossedTokens := [("perfectly", ""), ("dirty", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['d', 'i', 'r', 't', 'y'], [], [⟨['d', 'i', 'r', 't', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "dirty"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63a_slightly_dirty : Datum :=
  { id := "kennedy2007_63a_slightly_dirty"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly dirty"
    glossedTokens := [("slightly", ""), ("dirty", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['d', 'i', 'r', 't', 'y'], [], [⟨['d', 'i', 'r', 't', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "dirty"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63a_perfectly_worried : Datum :=
  { id := "kennedy2007_63a_perfectly_worried"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly worried"
    glossedTokens := [("perfectly", ""), ("worried", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 'd'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63a_slightly_worried : Datum :=
  { id := "kennedy2007_63a_slightly_worried"
    source := ⟨"kennedy-2007", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly worried"
    glossedTokens := [("slightly", ""), ("worried", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['w', 'o', 'r', 'r', 'i', 'e', 'd'], [], [⟨['w', 'o', 'r', 'r', 'i', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63b_perfectly_straight : Datum :=
  { id := "kennedy2007_63b_perfectly_straight"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly straight"
    glossedTokens := [("perfectly", ""), ("straight", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 't', 'r', 'a', 'i', 'g', 'h', 't'], [], [⟨['s', 't', 'r', 'a', 'i', 'g', 'h', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "straight"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63b_slightly_straight : Datum :=
  { id := "kennedy2007_63b_slightly_straight"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly straight"
    glossedTokens := [("slightly", ""), ("straight", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 't', 'r', 'a', 'i', 'g', 'h', 't'], [], [⟨['s', 't', 'r', 'a', 'i', 'g', 'h', 't'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "straight"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63b_perfectly_flat : Datum :=
  { id := "kennedy2007_63b_perfectly_flat"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly flat"
    glossedTokens := [("perfectly", ""), ("flat", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['f', 'l', 'a', 't'], [], [⟨['f', 'l', 'a', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "flat"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63b_slightly_flat : Datum :=
  { id := "kennedy2007_63b_slightly_flat"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly flat"
    glossedTokens := [("slightly", ""), ("flat", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['f', 'l', 'a', 't'], [], [⟨['f', 'l', 'a', 't'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "flat"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63b_perfectly_clean : Datum :=
  { id := "kennedy2007_63b_perfectly_clean"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly clean"
    glossedTokens := [("perfectly", ""), ("clean", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'l', 'e', 'a', 'n'], [], [⟨['c', 'l', 'e', 'a', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "clean"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63b_slightly_clean : Datum :=
  { id := "kennedy2007_63b_slightly_clean"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly clean"
    glossedTokens := [("slightly", ""), ("clean", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'l', 'e', 'a', 'n'], [], [⟨['c', 'l', 'e', 'a', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "clean"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_63b_perfectly_unworried : Datum :=
  { id := "kennedy2007_63b_perfectly_unworried"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly unworried"
    glossedTokens := [("perfectly", ""), ("unworried", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['u', 'n', 'w', 'o', 'r', 'r', 'i', 'e', 'd'], [], [⟨['u', 'n', 'w', 'o', 'r', 'r', 'i', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_63b_slightly_unworried : Datum :=
  { id := "kennedy2007_63b_slightly_unworried"
    source := ⟨"kennedy-2007", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly unworried"
    glossedTokens := [("slightly", ""), ("unworried", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['u', 'n', 'w', 'o', 'r', 'r', 'i', 'e', 'd'], [], [⟨['u', 'n', 'w', 'o', 'r', 'r', 'i', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64a_perfectly_certain : Datum :=
  { id := "kennedy2007_64a_perfectly_certain"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly certain"
    glossedTokens := [("perfectly", ""), ("certain", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], [⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "certain"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64a_slightly_certain : Datum :=
  { id := "kennedy2007_64a_slightly_certain"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly certain"
    glossedTokens := [("slightly", ""), ("certain", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], [⟨['c', 'e', 'r', 't', 'a', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "certain"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64a_perfectly_safe : Datum :=
  { id := "kennedy2007_64a_perfectly_safe"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly safe"
    glossedTokens := [("perfectly", ""), ("safe", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'a', 'f', 'e'], [], [⟨['s', 'a', 'f', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "safe"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64a_slightly_safe : Datum :=
  { id := "kennedy2007_64a_slightly_safe"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly safe"
    glossedTokens := [("slightly", ""), ("safe", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['s', 'a', 'f', 'e'], [], [⟨['s', 'a', 'f', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "safe"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64a_perfectly_pure : Datum :=
  { id := "kennedy2007_64a_perfectly_pure"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly pure"
    glossedTokens := [("perfectly", ""), ("pure", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['p', 'u', 'r', 'e'], [], [⟨['p', 'u', 'r', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "pure"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64a_slightly_pure : Datum :=
  { id := "kennedy2007_64a_slightly_pure"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly pure"
    glossedTokens := [("slightly", ""), ("pure", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['p', 'u', 'r', 'e'], [], [⟨['p', 'u', 'r', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "pure"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64a_perfectly_accurate : Datum :=
  { id := "kennedy2007_64a_perfectly_accurate"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly accurate"
    glossedTokens := [("perfectly", ""), ("accurate", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], [⟨['a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64a_slightly_accurate : Datum :=
  { id := "kennedy2007_64a_slightly_accurate"
    source := ⟨"kennedy-2007", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly accurate"
    glossedTokens := [("slightly", ""), ("accurate", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], [⟨['a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64b_perfectly_uncertain : Datum :=
  { id := "kennedy2007_64b_perfectly_uncertain"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly uncertain"
    glossedTokens := [("perfectly", ""), ("uncertain", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['u', 'n', 'c', 'e', 'r', 't', 'a', 'i', 'n'], [], [⟨['u', 'n', 'c', 'e', 'r', 't', 'a', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "uncertain"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64b_slightly_uncertain : Datum :=
  { id := "kennedy2007_64b_slightly_uncertain"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly uncertain"
    glossedTokens := [("slightly", ""), ("uncertain", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['u', 'n', 'c', 'e', 'r', 't', 'a', 'i', 'n'], [], [⟨['u', 'n', 'c', 'e', 'r', 't', 'a', 'i', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "uncertain"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64b_perfectly_dangerous : Datum :=
  { id := "kennedy2007_64b_perfectly_dangerous"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly dangerous"
    glossedTokens := [("perfectly", ""), ("dangerous", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['d', 'a', 'n', 'g', 'e', 'r', 'o', 'u', 's'], [], [⟨['d', 'a', 'n', 'g', 'e', 'r', 'o', 'u', 's'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "dangerous"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64b_slightly_dangerous : Datum :=
  { id := "kennedy2007_64b_slightly_dangerous"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly dangerous"
    glossedTokens := [("slightly", ""), ("dangerous", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['d', 'a', 'n', 'g', 'e', 'r', 'o', 'u', 's'], [], [⟨['d', 'a', 'n', 'g', 'e', 'r', 'o', 'u', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "dangerous"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64b_perfectly_impure : Datum :=
  { id := "kennedy2007_64b_perfectly_impure"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly impure"
    glossedTokens := [("perfectly", ""), ("impure", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['i', 'm', 'p', 'u', 'r', 'e'], [], [⟨['i', 'm', 'p', 'u', 'r', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64b_slightly_impure : Datum :=
  { id := "kennedy2007_64b_slightly_impure"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly impure"
    glossedTokens := [("slightly", ""), ("impure", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['i', 'm', 'p', 'u', 'r', 'e'], [], [⟨['i', 'm', 'p', 'u', 'r', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_64b_perfectly_inaccurate : Datum :=
  { id := "kennedy2007_64b_perfectly_inaccurate"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly inaccurate"
    glossedTokens := [("perfectly", ""), ("inaccurate", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['i', 'n', 'a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], [⟨['i', 'n', 'a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_64b_slightly_inaccurate : Datum :=
  { id := "kennedy2007_64b_slightly_inaccurate"
    source := ⟨"kennedy-2007", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly inaccurate"
    glossedTokens := [("slightly", ""), ("inaccurate", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['i', 'n', 'a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], [⟨['i', 'n', 'a', 'c', 'c', 'u', 'r', 'a', 't', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_65a_perfectly_full : Datum :=
  { id := "kennedy2007_65a_perfectly_full"
    source := ⟨"kennedy-2007", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly full"
    glossedTokens := [("perfectly", ""), ("full", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['f', 'u', 'l', 'l'], [], [⟨['f', 'u', 'l', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "full"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_65a_slightly_full : Datum :=
  { id := "kennedy2007_65a_slightly_full"
    source := ⟨"kennedy-2007", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly full"
    glossedTokens := [("slightly", ""), ("full", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['f', 'u', 'l', 'l'], [], [⟨['f', 'u', 'l', 'l'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "full"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_65a_perfectly_open : Datum :=
  { id := "kennedy2007_65a_perfectly_open"
    source := ⟨"kennedy-2007", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly open"
    glossedTokens := [("perfectly", ""), ("open", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['o', 'p', 'e', 'n'], [], [⟨['o', 'p', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "open"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_65a_slightly_open : Datum :=
  { id := "kennedy2007_65a_slightly_open"
    source := ⟨"kennedy-2007", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly open"
    glossedTokens := [("slightly", ""), ("open", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['o', 'p', 'e', 'n'], [], [⟨['o', 'p', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "open"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_65a_perfectly_opaque : Datum :=
  { id := "kennedy2007_65a_perfectly_opaque"
    source := ⟨"kennedy-2007", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly opaque"
    glossedTokens := [("perfectly", ""), ("opaque", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['o', 'p', 'a', 'q', 'u', 'e'], [], [⟨['o', 'p', 'a', 'q', 'u', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_65a_slightly_opaque : Datum :=
  { id := "kennedy2007_65a_slightly_opaque"
    source := ⟨"kennedy-2007", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly opaque"
    glossedTokens := [("slightly", ""), ("opaque", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['o', 'p', 'a', 'q', 'u', 'e'], [], [⟨['o', 'p', 'a', 'q', 'u', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_65b_perfectly_empty : Datum :=
  { id := "kennedy2007_65b_perfectly_empty"
    source := ⟨"kennedy-2007", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly empty"
    glossedTokens := [("perfectly", ""), ("empty", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['e', 'm', 'p', 't', 'y'], [], [⟨['e', 'm', 'p', 't', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "empty"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_65b_slightly_empty : Datum :=
  { id := "kennedy2007_65b_slightly_empty"
    source := ⟨"kennedy-2007", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly empty"
    glossedTokens := [("slightly", ""), ("empty", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['e', 'm', 'p', 't', 'y'], [], [⟨['e', 'm', 'p', 't', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "empty"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_65b_perfectly_closed : Datum :=
  { id := "kennedy2007_65b_perfectly_closed"
    source := ⟨"kennedy-2007", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly closed"
    glossedTokens := [("perfectly", ""), ("closed", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'l', 'o', 's', 'e', 'd'], [], [⟨['c', 'l', 'o', 's', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "closed"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_65b_slightly_closed : Datum :=
  { id := "kennedy2007_65b_slightly_closed"
    source := ⟨"kennedy-2007", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly closed"
    glossedTokens := [("slightly", ""), ("closed", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'l', 'o', 's', 'e', 'd'], [], [⟨['c', 'l', 'o', 's', 'e', 'd'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", some "closed"⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def ex_65b_perfectly_transparent : Datum :=
  { id := "kennedy2007_65b_perfectly_transparent"
    source := ⟨"kennedy-2007", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "perfectly transparent"
    glossedTokens := [("perfectly", ""), ("transparent", "")]
    glossedWords := [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], [⟨['p', 'e', 'r', 'f', 'e', 'c', 't', 'l', 'y'], [], none⟩]⟩, ⟨['t', 'r', 'a', 'n', 's', 'p', 'a', 'r', 'e', 'n', 't'], [], [⟨['t', 'r', 'a', 'n', 's', 'p', 'a', 'r', 'e', 'n', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "perfectly")] }

def ex_65b_slightly_transparent : Datum :=
  { id := "kennedy2007_65b_slightly_transparent"
    source := ⟨"kennedy-2007", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "slightly transparent"
    glossedTokens := [("slightly", ""), ("transparent", "")]
    glossedWords := [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], [⟨['s', 'l', 'i', 'g', 'h', 't', 'l', 'y'], [], none⟩]⟩, ⟨['t', 'r', 'a', 'n', 's', 'p', 'a', 'r', 'e', 'n', 't'], [], [⟨['t', 'r', 'a', 'n', 's', 'p', 'a', 'r', 'e', 'n', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "adjective", none⟩]
    paperFeatures := [("section", "4.2"), ("modifier", "slightly")] }

def all : List Datum := [ex_62a_perfectly_tall, ex_62a_slightly_tall, ex_62a_perfectly_deep, ex_62a_slightly_deep, ex_62a_perfectly_expensive, ex_62a_slightly_expensive, ex_62a_perfectly_likely, ex_62a_slightly_likely, ex_62b_perfectly_short, ex_62b_slightly_short, ex_62b_perfectly_shallow, ex_62b_slightly_shallow, ex_62b_perfectly_inexpensive, ex_62b_slightly_inexpensive, ex_62b_perfectly_unlikely, ex_62b_slightly_unlikely, ex_63a_perfectly_bent, ex_63a_slightly_bent, ex_63a_perfectly_bumpy, ex_63a_slightly_bumpy, ex_63a_perfectly_dirty, ex_63a_slightly_dirty, ex_63a_perfectly_worried, ex_63a_slightly_worried, ex_63b_perfectly_straight, ex_63b_slightly_straight, ex_63b_perfectly_flat, ex_63b_slightly_flat, ex_63b_perfectly_clean, ex_63b_slightly_clean, ex_63b_perfectly_unworried, ex_63b_slightly_unworried, ex_64a_perfectly_certain, ex_64a_slightly_certain, ex_64a_perfectly_safe, ex_64a_slightly_safe, ex_64a_perfectly_pure, ex_64a_slightly_pure, ex_64a_perfectly_accurate, ex_64a_slightly_accurate, ex_64b_perfectly_uncertain, ex_64b_slightly_uncertain, ex_64b_perfectly_dangerous, ex_64b_slightly_dangerous, ex_64b_perfectly_impure, ex_64b_slightly_impure, ex_64b_perfectly_inaccurate, ex_64b_slightly_inaccurate, ex_65a_perfectly_full, ex_65a_slightly_full, ex_65a_perfectly_open, ex_65a_slightly_open, ex_65a_perfectly_opaque, ex_65a_slightly_opaque, ex_65b_perfectly_empty, ex_65b_slightly_empty, ex_65b_perfectly_closed, ex_65b_slightly_closed, ex_65b_perfectly_transparent, ex_65b_slightly_transparent]

/-- The degree modifiers the paper uses to probe for an endpoint. -/
inductive Modifier where
  /-- perfectly: picks out a maximal degree -/
  | perfectly
  /-- slightly: picks out a minimal degree -/
  | slightly
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `modifier`. -/
def modifier (e : Datum) : Option Modifier :=
  e.parse? "modifier" [("perfectly", .perfectly), ("slightly", .slightly)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- adjective: the adjective under test -/
  | adjective
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("adjective", .adjective)]

/-- The adjectives under test that the English adjectives file has. -/
inductive Lexeme where
  /-- tall: English tall -/
  | tall
  /-- deep: English deep -/
  | deep
  /-- expensive: English expensive -/
  | expensive
  /-- short: English short -/
  | short
  /-- shallow: English shallow -/
  | shallow
  /-- bent: English bent -/
  | bent
  /-- dirty: English dirty -/
  | dirty
  /-- straight: English straight -/
  | straight
  /-- flat: English flat -/
  | flat
  /-- clean: English clean -/
  | clean
  /-- certain: English certain -/
  | certain
  /-- safe: English safe -/
  | safe
  /-- pure: English pure -/
  | pure
  /-- uncertain: English uncertain -/
  | uncertain
  /-- dangerous: English dangerous -/
  | dangerous
  /-- full: English full -/
  | full
  /-- open: English open -/
  | openAdj
  /-- empty: English empty -/
  | empty
  /-- closed: English closed -/
  | closed
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("tall", .tall), ("deep", .deep), ("expensive", .expensive), ("short", .short), ("shallow", .shallow), ("bent", .bent), ("dirty", .dirty), ("straight", .straight), ("flat", .flat), ("clean", .clean), ("certain", .certain), ("safe", .safe), ("pure", .pure), ("uncertain", .uncertain), ("dangerous", .dangerous), ("full", .full), ("open", .openAdj), ("empty", .empty), ("closed", .closed)])

/-- The modifier judgments of (62)–(65), one per modifier and adjective. -/
inductive Example where
  | ex_62a_perfectly_tall
  | ex_62a_slightly_tall
  | ex_62a_perfectly_deep
  | ex_62a_slightly_deep
  | ex_62a_perfectly_expensive
  | ex_62a_slightly_expensive
  | ex_62a_perfectly_likely
  | ex_62a_slightly_likely
  | ex_62b_perfectly_short
  | ex_62b_slightly_short
  | ex_62b_perfectly_shallow
  | ex_62b_slightly_shallow
  | ex_62b_perfectly_inexpensive
  | ex_62b_slightly_inexpensive
  | ex_62b_perfectly_unlikely
  | ex_62b_slightly_unlikely
  | ex_63a_perfectly_bent
  | ex_63a_slightly_bent
  | ex_63a_perfectly_bumpy
  | ex_63a_slightly_bumpy
  | ex_63a_perfectly_dirty
  | ex_63a_slightly_dirty
  | ex_63a_perfectly_worried
  | ex_63a_slightly_worried
  | ex_63b_perfectly_straight
  | ex_63b_slightly_straight
  | ex_63b_perfectly_flat
  | ex_63b_slightly_flat
  | ex_63b_perfectly_clean
  | ex_63b_slightly_clean
  | ex_63b_perfectly_unworried
  | ex_63b_slightly_unworried
  | ex_64a_perfectly_certain
  | ex_64a_slightly_certain
  | ex_64a_perfectly_safe
  | ex_64a_slightly_safe
  | ex_64a_perfectly_pure
  | ex_64a_slightly_pure
  | ex_64a_perfectly_accurate
  | ex_64a_slightly_accurate
  | ex_64b_perfectly_uncertain
  | ex_64b_slightly_uncertain
  | ex_64b_perfectly_dangerous
  | ex_64b_slightly_dangerous
  | ex_64b_perfectly_impure
  | ex_64b_slightly_impure
  | ex_64b_perfectly_inaccurate
  | ex_64b_slightly_inaccurate
  | ex_65a_perfectly_full
  | ex_65a_slightly_full
  | ex_65a_perfectly_open
  | ex_65a_slightly_open
  | ex_65a_perfectly_opaque
  | ex_65a_slightly_opaque
  | ex_65b_perfectly_empty
  | ex_65b_slightly_empty
  | ex_65b_perfectly_closed
  | ex_65b_slightly_closed
  | ex_65b_perfectly_transparent
  | ex_65b_slightly_transparent
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_62a_perfectly_tall, .ex_62a_slightly_tall, .ex_62a_perfectly_deep, .ex_62a_slightly_deep,
    .ex_62a_perfectly_expensive, .ex_62a_slightly_expensive, .ex_62a_perfectly_likely,
    .ex_62a_slightly_likely, .ex_62b_perfectly_short, .ex_62b_slightly_short,
    .ex_62b_perfectly_shallow, .ex_62b_slightly_shallow, .ex_62b_perfectly_inexpensive,
    .ex_62b_slightly_inexpensive, .ex_62b_perfectly_unlikely, .ex_62b_slightly_unlikely,
    .ex_63a_perfectly_bent, .ex_63a_slightly_bent, .ex_63a_perfectly_bumpy,
    .ex_63a_slightly_bumpy, .ex_63a_perfectly_dirty, .ex_63a_slightly_dirty,
    .ex_63a_perfectly_worried, .ex_63a_slightly_worried, .ex_63b_perfectly_straight,
    .ex_63b_slightly_straight, .ex_63b_perfectly_flat, .ex_63b_slightly_flat,
    .ex_63b_perfectly_clean, .ex_63b_slightly_clean, .ex_63b_perfectly_unworried,
    .ex_63b_slightly_unworried, .ex_64a_perfectly_certain, .ex_64a_slightly_certain,
    .ex_64a_perfectly_safe, .ex_64a_slightly_safe, .ex_64a_perfectly_pure, .ex_64a_slightly_pure,
    .ex_64a_perfectly_accurate, .ex_64a_slightly_accurate, .ex_64b_perfectly_uncertain,
    .ex_64b_slightly_uncertain, .ex_64b_perfectly_dangerous, .ex_64b_slightly_dangerous,
    .ex_64b_perfectly_impure, .ex_64b_slightly_impure, .ex_64b_perfectly_inaccurate,
    .ex_64b_slightly_inaccurate, .ex_65a_perfectly_full, .ex_65a_slightly_full,
    .ex_65a_perfectly_open, .ex_65a_slightly_open, .ex_65a_perfectly_opaque,
    .ex_65a_slightly_opaque, .ex_65b_perfectly_empty, .ex_65b_slightly_empty,
    .ex_65b_perfectly_closed, .ex_65b_slightly_closed, .ex_65b_perfectly_transparent,
    .ex_65b_slightly_transparent]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_62a_perfectly_tall => _root_.Kennedy2007.Examples.ex_62a_perfectly_tall
  | .ex_62a_slightly_tall => _root_.Kennedy2007.Examples.ex_62a_slightly_tall
  | .ex_62a_perfectly_deep => _root_.Kennedy2007.Examples.ex_62a_perfectly_deep
  | .ex_62a_slightly_deep => _root_.Kennedy2007.Examples.ex_62a_slightly_deep
  | .ex_62a_perfectly_expensive => _root_.Kennedy2007.Examples.ex_62a_perfectly_expensive
  | .ex_62a_slightly_expensive => _root_.Kennedy2007.Examples.ex_62a_slightly_expensive
  | .ex_62a_perfectly_likely => _root_.Kennedy2007.Examples.ex_62a_perfectly_likely
  | .ex_62a_slightly_likely => _root_.Kennedy2007.Examples.ex_62a_slightly_likely
  | .ex_62b_perfectly_short => _root_.Kennedy2007.Examples.ex_62b_perfectly_short
  | .ex_62b_slightly_short => _root_.Kennedy2007.Examples.ex_62b_slightly_short
  | .ex_62b_perfectly_shallow => _root_.Kennedy2007.Examples.ex_62b_perfectly_shallow
  | .ex_62b_slightly_shallow => _root_.Kennedy2007.Examples.ex_62b_slightly_shallow
  | .ex_62b_perfectly_inexpensive => _root_.Kennedy2007.Examples.ex_62b_perfectly_inexpensive
  | .ex_62b_slightly_inexpensive => _root_.Kennedy2007.Examples.ex_62b_slightly_inexpensive
  | .ex_62b_perfectly_unlikely => _root_.Kennedy2007.Examples.ex_62b_perfectly_unlikely
  | .ex_62b_slightly_unlikely => _root_.Kennedy2007.Examples.ex_62b_slightly_unlikely
  | .ex_63a_perfectly_bent => _root_.Kennedy2007.Examples.ex_63a_perfectly_bent
  | .ex_63a_slightly_bent => _root_.Kennedy2007.Examples.ex_63a_slightly_bent
  | .ex_63a_perfectly_bumpy => _root_.Kennedy2007.Examples.ex_63a_perfectly_bumpy
  | .ex_63a_slightly_bumpy => _root_.Kennedy2007.Examples.ex_63a_slightly_bumpy
  | .ex_63a_perfectly_dirty => _root_.Kennedy2007.Examples.ex_63a_perfectly_dirty
  | .ex_63a_slightly_dirty => _root_.Kennedy2007.Examples.ex_63a_slightly_dirty
  | .ex_63a_perfectly_worried => _root_.Kennedy2007.Examples.ex_63a_perfectly_worried
  | .ex_63a_slightly_worried => _root_.Kennedy2007.Examples.ex_63a_slightly_worried
  | .ex_63b_perfectly_straight => _root_.Kennedy2007.Examples.ex_63b_perfectly_straight
  | .ex_63b_slightly_straight => _root_.Kennedy2007.Examples.ex_63b_slightly_straight
  | .ex_63b_perfectly_flat => _root_.Kennedy2007.Examples.ex_63b_perfectly_flat
  | .ex_63b_slightly_flat => _root_.Kennedy2007.Examples.ex_63b_slightly_flat
  | .ex_63b_perfectly_clean => _root_.Kennedy2007.Examples.ex_63b_perfectly_clean
  | .ex_63b_slightly_clean => _root_.Kennedy2007.Examples.ex_63b_slightly_clean
  | .ex_63b_perfectly_unworried => _root_.Kennedy2007.Examples.ex_63b_perfectly_unworried
  | .ex_63b_slightly_unworried => _root_.Kennedy2007.Examples.ex_63b_slightly_unworried
  | .ex_64a_perfectly_certain => _root_.Kennedy2007.Examples.ex_64a_perfectly_certain
  | .ex_64a_slightly_certain => _root_.Kennedy2007.Examples.ex_64a_slightly_certain
  | .ex_64a_perfectly_safe => _root_.Kennedy2007.Examples.ex_64a_perfectly_safe
  | .ex_64a_slightly_safe => _root_.Kennedy2007.Examples.ex_64a_slightly_safe
  | .ex_64a_perfectly_pure => _root_.Kennedy2007.Examples.ex_64a_perfectly_pure
  | .ex_64a_slightly_pure => _root_.Kennedy2007.Examples.ex_64a_slightly_pure
  | .ex_64a_perfectly_accurate => _root_.Kennedy2007.Examples.ex_64a_perfectly_accurate
  | .ex_64a_slightly_accurate => _root_.Kennedy2007.Examples.ex_64a_slightly_accurate
  | .ex_64b_perfectly_uncertain => _root_.Kennedy2007.Examples.ex_64b_perfectly_uncertain
  | .ex_64b_slightly_uncertain => _root_.Kennedy2007.Examples.ex_64b_slightly_uncertain
  | .ex_64b_perfectly_dangerous => _root_.Kennedy2007.Examples.ex_64b_perfectly_dangerous
  | .ex_64b_slightly_dangerous => _root_.Kennedy2007.Examples.ex_64b_slightly_dangerous
  | .ex_64b_perfectly_impure => _root_.Kennedy2007.Examples.ex_64b_perfectly_impure
  | .ex_64b_slightly_impure => _root_.Kennedy2007.Examples.ex_64b_slightly_impure
  | .ex_64b_perfectly_inaccurate => _root_.Kennedy2007.Examples.ex_64b_perfectly_inaccurate
  | .ex_64b_slightly_inaccurate => _root_.Kennedy2007.Examples.ex_64b_slightly_inaccurate
  | .ex_65a_perfectly_full => _root_.Kennedy2007.Examples.ex_65a_perfectly_full
  | .ex_65a_slightly_full => _root_.Kennedy2007.Examples.ex_65a_slightly_full
  | .ex_65a_perfectly_open => _root_.Kennedy2007.Examples.ex_65a_perfectly_open
  | .ex_65a_slightly_open => _root_.Kennedy2007.Examples.ex_65a_slightly_open
  | .ex_65a_perfectly_opaque => _root_.Kennedy2007.Examples.ex_65a_perfectly_opaque
  | .ex_65a_slightly_opaque => _root_.Kennedy2007.Examples.ex_65a_slightly_opaque
  | .ex_65b_perfectly_empty => _root_.Kennedy2007.Examples.ex_65b_perfectly_empty
  | .ex_65b_slightly_empty => _root_.Kennedy2007.Examples.ex_65b_slightly_empty
  | .ex_65b_perfectly_closed => _root_.Kennedy2007.Examples.ex_65b_perfectly_closed
  | .ex_65b_slightly_closed => _root_.Kennedy2007.Examples.ex_65b_slightly_closed
  | .ex_65b_perfectly_transparent => _root_.Kennedy2007.Examples.ex_65b_perfectly_transparent
  | .ex_65b_slightly_transparent => _root_.Kennedy2007.Examples.ex_65b_slightly_transparent

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Kennedy2007.Examples.all := rfl

/-- The value the example records under `modifier`. -/
def Example.modifier : Example → Option Modifier
  | .ex_62a_perfectly_tall => some .perfectly
  | .ex_62a_slightly_tall => some .slightly
  | .ex_62a_perfectly_deep => some .perfectly
  | .ex_62a_slightly_deep => some .slightly
  | .ex_62a_perfectly_expensive => some .perfectly
  | .ex_62a_slightly_expensive => some .slightly
  | .ex_62a_perfectly_likely => some .perfectly
  | .ex_62a_slightly_likely => some .slightly
  | .ex_62b_perfectly_short => some .perfectly
  | .ex_62b_slightly_short => some .slightly
  | .ex_62b_perfectly_shallow => some .perfectly
  | .ex_62b_slightly_shallow => some .slightly
  | .ex_62b_perfectly_inexpensive => some .perfectly
  | .ex_62b_slightly_inexpensive => some .slightly
  | .ex_62b_perfectly_unlikely => some .perfectly
  | .ex_62b_slightly_unlikely => some .slightly
  | .ex_63a_perfectly_bent => some .perfectly
  | .ex_63a_slightly_bent => some .slightly
  | .ex_63a_perfectly_bumpy => some .perfectly
  | .ex_63a_slightly_bumpy => some .slightly
  | .ex_63a_perfectly_dirty => some .perfectly
  | .ex_63a_slightly_dirty => some .slightly
  | .ex_63a_perfectly_worried => some .perfectly
  | .ex_63a_slightly_worried => some .slightly
  | .ex_63b_perfectly_straight => some .perfectly
  | .ex_63b_slightly_straight => some .slightly
  | .ex_63b_perfectly_flat => some .perfectly
  | .ex_63b_slightly_flat => some .slightly
  | .ex_63b_perfectly_clean => some .perfectly
  | .ex_63b_slightly_clean => some .slightly
  | .ex_63b_perfectly_unworried => some .perfectly
  | .ex_63b_slightly_unworried => some .slightly
  | .ex_64a_perfectly_certain => some .perfectly
  | .ex_64a_slightly_certain => some .slightly
  | .ex_64a_perfectly_safe => some .perfectly
  | .ex_64a_slightly_safe => some .slightly
  | .ex_64a_perfectly_pure => some .perfectly
  | .ex_64a_slightly_pure => some .slightly
  | .ex_64a_perfectly_accurate => some .perfectly
  | .ex_64a_slightly_accurate => some .slightly
  | .ex_64b_perfectly_uncertain => some .perfectly
  | .ex_64b_slightly_uncertain => some .slightly
  | .ex_64b_perfectly_dangerous => some .perfectly
  | .ex_64b_slightly_dangerous => some .slightly
  | .ex_64b_perfectly_impure => some .perfectly
  | .ex_64b_slightly_impure => some .slightly
  | .ex_64b_perfectly_inaccurate => some .perfectly
  | .ex_64b_slightly_inaccurate => some .slightly
  | .ex_65a_perfectly_full => some .perfectly
  | .ex_65a_slightly_full => some .slightly
  | .ex_65a_perfectly_open => some .perfectly
  | .ex_65a_slightly_open => some .slightly
  | .ex_65a_perfectly_opaque => some .perfectly
  | .ex_65a_slightly_opaque => some .slightly
  | .ex_65b_perfectly_empty => some .perfectly
  | .ex_65b_slightly_empty => some .slightly
  | .ex_65b_perfectly_closed => some .perfectly
  | .ex_65b_slightly_closed => some .slightly
  | .ex_65b_perfectly_transparent => some .perfectly
  | .ex_65b_slightly_transparent => some .slightly

theorem Example.modifier_datum :
    ∀ x : Example, _root_.Kennedy2007.Examples.modifier x.datum = x.modifier := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_62a_perfectly_tall => [(.adjective, .tall)]
  | .ex_62a_slightly_tall => [(.adjective, .tall)]
  | .ex_62a_perfectly_deep => [(.adjective, .deep)]
  | .ex_62a_slightly_deep => [(.adjective, .deep)]
  | .ex_62a_perfectly_expensive => [(.adjective, .expensive)]
  | .ex_62a_slightly_expensive => [(.adjective, .expensive)]
  | .ex_62a_perfectly_likely => []
  | .ex_62a_slightly_likely => []
  | .ex_62b_perfectly_short => [(.adjective, .short)]
  | .ex_62b_slightly_short => [(.adjective, .short)]
  | .ex_62b_perfectly_shallow => [(.adjective, .shallow)]
  | .ex_62b_slightly_shallow => [(.adjective, .shallow)]
  | .ex_62b_perfectly_inexpensive => []
  | .ex_62b_slightly_inexpensive => []
  | .ex_62b_perfectly_unlikely => []
  | .ex_62b_slightly_unlikely => []
  | .ex_63a_perfectly_bent => [(.adjective, .bent)]
  | .ex_63a_slightly_bent => [(.adjective, .bent)]
  | .ex_63a_perfectly_bumpy => []
  | .ex_63a_slightly_bumpy => []
  | .ex_63a_perfectly_dirty => [(.adjective, .dirty)]
  | .ex_63a_slightly_dirty => [(.adjective, .dirty)]
  | .ex_63a_perfectly_worried => []
  | .ex_63a_slightly_worried => []
  | .ex_63b_perfectly_straight => [(.adjective, .straight)]
  | .ex_63b_slightly_straight => [(.adjective, .straight)]
  | .ex_63b_perfectly_flat => [(.adjective, .flat)]
  | .ex_63b_slightly_flat => [(.adjective, .flat)]
  | .ex_63b_perfectly_clean => [(.adjective, .clean)]
  | .ex_63b_slightly_clean => [(.adjective, .clean)]
  | .ex_63b_perfectly_unworried => []
  | .ex_63b_slightly_unworried => []
  | .ex_64a_perfectly_certain => [(.adjective, .certain)]
  | .ex_64a_slightly_certain => [(.adjective, .certain)]
  | .ex_64a_perfectly_safe => [(.adjective, .safe)]
  | .ex_64a_slightly_safe => [(.adjective, .safe)]
  | .ex_64a_perfectly_pure => [(.adjective, .pure)]
  | .ex_64a_slightly_pure => [(.adjective, .pure)]
  | .ex_64a_perfectly_accurate => []
  | .ex_64a_slightly_accurate => []
  | .ex_64b_perfectly_uncertain => [(.adjective, .uncertain)]
  | .ex_64b_slightly_uncertain => [(.adjective, .uncertain)]
  | .ex_64b_perfectly_dangerous => [(.adjective, .dangerous)]
  | .ex_64b_slightly_dangerous => [(.adjective, .dangerous)]
  | .ex_64b_perfectly_impure => []
  | .ex_64b_slightly_impure => []
  | .ex_64b_perfectly_inaccurate => []
  | .ex_64b_slightly_inaccurate => []
  | .ex_65a_perfectly_full => [(.adjective, .full)]
  | .ex_65a_slightly_full => [(.adjective, .full)]
  | .ex_65a_perfectly_open => [(.adjective, .openAdj)]
  | .ex_65a_slightly_open => [(.adjective, .openAdj)]
  | .ex_65a_perfectly_opaque => []
  | .ex_65a_slightly_opaque => []
  | .ex_65b_perfectly_empty => [(.adjective, .empty)]
  | .ex_65b_slightly_empty => [(.adjective, .empty)]
  | .ex_65b_perfectly_closed => [(.adjective, .closed)]
  | .ex_65b_slightly_closed => [(.adjective, .closed)]
  | .ex_65b_perfectly_transparent => []
  | .ex_65b_slightly_transparent => []

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.Kennedy2007.Examples.label? · = some l)).filterMap _root_.Kennedy2007.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end Kennedy2007.Examples
