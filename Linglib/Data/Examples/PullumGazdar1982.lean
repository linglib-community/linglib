module

public import Linglib.Data.Examples.Schema
public import Mathlib.Tactic.DeriveFintype

/-!
# `PullumGazdar1982` — typed example data

Auto-generated from `Linglib/Data/Examples/PullumGazdar1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace PullumGazdar1982.Examples`.
-/

@[expose] public section

namespace PullumGazdar1982.Examples

def ex18a : Datum :=
  { id := "pullumgazdar1982_ex18a"
    source := ⟨"pullum-gazdar-1982", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smokes and drinks respectively."
    glossedTokens := [("The", ""), ("woman", ""), ("and", ""), ("the", ""), ("men", ""), ("smokes", ""), ("and", ""), ("drinks", ""), ("respectively", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'a', 'n'], [], [⟨['w', 'o', 'm', 'a', 'n'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'n'], [], [⟨['m', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'm', 'o', 'k', 'e', 's'], [], [⟨['s', 'm', 'o', 'k', 'e', 's'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'n', 'k', 's'], [], [⟨['d', 'r', 'i', 'n', 'k', 's'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], [⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "woman"⟩, ⟨4, 1, "subject", some "man"⟩, ⟨5, 1, "verb", some "smoke"⟩, ⟨7, 1, "verb", some "drink"⟩]
    paperFeatures := [] }

def ex18b : Datum :=
  { id := "pullumgazdar1982_ex18b"
    source := ⟨"pullum-gazdar-1982", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smokes and drink respectively."
    glossedTokens := [("The", ""), ("woman", ""), ("and", ""), ("the", ""), ("men", ""), ("smokes", ""), ("and", ""), ("drink", ""), ("respectively", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'a', 'n'], [], [⟨['w', 'o', 'm', 'a', 'n'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'n'], [], [⟨['m', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'm', 'o', 'k', 'e', 's'], [], [⟨['s', 'm', 'o', 'k', 'e', 's'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'n', 'k'], [], [⟨['d', 'r', 'i', 'n', 'k'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], [⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "woman"⟩, ⟨4, 1, "subject", some "man"⟩, ⟨5, 1, "verb", some "smoke"⟩, ⟨7, 1, "verb", some "drink"⟩]
    paperFeatures := [] }

def ex18c : Datum :=
  { id := "pullumgazdar1982_ex18c"
    source := ⟨"pullum-gazdar-1982", "(18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smoke and drinks respectively."
    glossedTokens := [("The", ""), ("woman", ""), ("and", ""), ("the", ""), ("men", ""), ("smoke", ""), ("and", ""), ("drinks", ""), ("respectively", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'a', 'n'], [], [⟨['w', 'o', 'm', 'a', 'n'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'n'], [], [⟨['m', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'm', 'o', 'k', 'e'], [], [⟨['s', 'm', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'n', 'k', 's'], [], [⟨['d', 'r', 'i', 'n', 'k', 's'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], [⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "woman"⟩, ⟨4, 1, "subject", some "man"⟩, ⟨5, 1, "verb", some "smoke"⟩, ⟨7, 1, "verb", some "drink"⟩]
    paperFeatures := [] }

def ex18d : Datum :=
  { id := "pullumgazdar1982_ex18d"
    source := ⟨"pullum-gazdar-1982", "(18d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The woman and the men smoke and drink respectively."
    glossedTokens := [("The", ""), ("woman", ""), ("and", ""), ("the", ""), ("men", ""), ("smoke", ""), ("and", ""), ("drink", ""), ("respectively", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'a', 'n'], [], [⟨['w', 'o', 'm', 'a', 'n'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'e', 'n'], [], [⟨['m', 'e', 'n'], [], none⟩]⟩, ⟨['s', 'm', 'o', 'k', 'e'], [], [⟨['s', 'm', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'n', 'k'], [], [⟨['d', 'r', 'i', 'n', 'k'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], [⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "woman"⟩, ⟨4, 1, "subject", some "man"⟩, ⟨5, 1, "verb", some "smoke"⟩, ⟨7, 1, "verb", some "drink"⟩]
    paperFeatures := [] }

def ex19a : Datum :=
  { id := "pullumgazdar1982_ex19a"
    source := ⟨"pullum-gazdar-1982", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man and the woman smokes and drinks respectively."
    glossedTokens := [("The", ""), ("man", ""), ("and", ""), ("the", ""), ("woman", ""), ("smokes", ""), ("and", ""), ("drinks", ""), ("respectively", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'a', 'n'], [], [⟨['m', 'a', 'n'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'a', 'n'], [], [⟨['w', 'o', 'm', 'a', 'n'], [], none⟩]⟩, ⟨['s', 'm', 'o', 'k', 'e', 's'], [], [⟨['s', 'm', 'o', 'k', 'e', 's'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'n', 'k', 's'], [], [⟨['d', 'r', 'i', 'n', 'k', 's'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], [⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "man"⟩, ⟨4, 1, "subject", some "woman"⟩, ⟨5, 1, "verb", some "smoke"⟩, ⟨7, 1, "verb", some "drink"⟩]
    paperFeatures := [] }

def ex19b : Datum :=
  { id := "pullumgazdar1982_ex19b"
    source := ⟨"pullum-gazdar-1982", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man and the woman smoke and drink respectively."
    glossedTokens := [("The", ""), ("man", ""), ("and", ""), ("the", ""), ("woman", ""), ("smoke", ""), ("and", ""), ("drink", ""), ("respectively", "")]
    glossedWords := [⟨['T', 'h', 'e'], [], [⟨['T', 'h', 'e'], [], none⟩]⟩, ⟨['m', 'a', 'n'], [], [⟨['m', 'a', 'n'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['w', 'o', 'm', 'a', 'n'], [], [⟨['w', 'o', 'm', 'a', 'n'], [], none⟩]⟩, ⟨['s', 'm', 'o', 'k', 'e'], [], [⟨['s', 'm', 'o', 'k', 'e'], [], none⟩]⟩, ⟨['a', 'n', 'd'], [], [⟨['a', 'n', 'd'], [], none⟩]⟩, ⟨['d', 'r', 'i', 'n', 'k'], [], [⟨['d', 'r', 'i', 'n', 'k'], [], none⟩]⟩, ⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], [⟨['r', 'e', 's', 'p', 'e', 'c', 't', 'i', 'v', 'e', 'l', 'y'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "subject", some "man"⟩, ⟨4, 1, "subject", some "woman"⟩, ⟨5, 1, "verb", some "smoke"⟩, ⟨7, 1, "verb", some "drink"⟩]
    paperFeatures := [] }

def ex25 : Datum :=
  { id := "pullumgazdar1982_ex25"
    source := ⟨"pullum-gazdar-1982", "(25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch laat zien schrijven"
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Marie", "Marie"), ("Pieter", "Pieter"), ("Arabisch", "Arabic"), ("laat", "let"), ("zien", "see"), ("schrijven", "write")]
    glossedWords := [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], [⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], [⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], none⟩]⟩, ⟨['l', 'a', 'a', 't'], ['l', 'e', 't'], [⟨['l', 'a', 'a', 't'], ['l', 'e', 't'], none⟩]⟩, ⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], [⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], [⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 6, "verb phrase", none⟩, ⟨2, 1, "word", some "Marie"⟩, ⟨3, 1, "word", some "Pieter"⟩, ⟨4, 1, "word", some "Arabisch"⟩, ⟨5, 1, "word", some "laten"⟩, ⟨6, 1, "word", some "zien"⟩, ⟨7, 1, "word", some "schrijven"⟩]
    paperFeatures := [] }

def ex26 : Datum :=
  { id := "pullumgazdar1982_ex26"
    source := ⟨"pullum-gazdar-1982", "(26)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch laat zien liegen"
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Marie", "Marie"), ("Pieter", "Pieter"), ("Arabisch", "Arabic"), ("laat", "let"), ("zien", "see"), ("liegen", "lie")]
    glossedWords := [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], [⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], [⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], none⟩]⟩, ⟨['l', 'a', 'a', 't'], ['l', 'e', 't'], [⟨['l', 'a', 'a', 't'], ['l', 'e', 't'], none⟩]⟩, ⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], [⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['l', 'i', 'e', 'g', 'e', 'n'], ['l', 'i', 'e'], [⟨['l', 'i', 'e', 'g', 'e', 'n'], ['l', 'i', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 6, "verb phrase", none⟩, ⟨2, 1, "word", some "Marie"⟩, ⟨3, 1, "word", some "Pieter"⟩, ⟨4, 1, "word", some "Arabisch"⟩, ⟨5, 1, "word", some "laten"⟩, ⟨6, 1, "word", some "zien"⟩, ⟨7, 1, "word", some "liegen"⟩]
    paperFeatures := [] }

def ex27 : Datum :=
  { id := "pullumgazdar1982_ex27"
    source := ⟨"pullum-gazdar-1982", "(27)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch Hans laat zien schrijven"
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Marie", "Marie"), ("Pieter", "Pieter"), ("Arabisch", "Arabic"), ("Hans", "Hans"), ("laat", "let"), ("zien", "see"), ("schrijven", "write")]
    glossedWords := [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], [⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], [⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], none⟩]⟩, ⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['l', 'a', 'a', 't'], ['l', 'e', 't'], [⟨['l', 'a', 'a', 't'], ['l', 'e', 't'], none⟩]⟩, ⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], [⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], [⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 7, "verb phrase", none⟩, ⟨2, 1, "word", some "Marie"⟩, ⟨3, 1, "word", some "Pieter"⟩, ⟨4, 1, "word", some "Arabisch"⟩, ⟨5, 1, "word", some "Hans"⟩, ⟨6, 1, "word", some "laten"⟩, ⟨7, 1, "word", some "zien"⟩, ⟨8, 1, "word", some "schrijven"⟩]
    paperFeatures := [] }

def ex28 : Datum :=
  { id := "pullumgazdar1982_ex28"
    source := ⟨"pullum-gazdar-1982", "(28)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat Jan Marie Pieter Arabisch wil laten zien schrijven"
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Marie", "Marie"), ("Pieter", "Pieter"), ("Arabisch", "Arabic"), ("wil", "will"), ("laten", "let"), ("zien", "see"), ("schrijven", "write")]
    glossedWords := [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], [⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], [⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], none⟩]⟩, ⟨['w', 'i', 'l'], ['w', 'i', 'l', 'l'], [⟨['w', 'i', 'l'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['l', 'a', 't', 'e', 'n'], ['l', 'e', 't'], [⟨['l', 'a', 't', 'e', 'n'], ['l', 'e', 't'], none⟩]⟩, ⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], [⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], [⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 7, "verb phrase", none⟩, ⟨2, 1, "word", some "Marie"⟩, ⟨3, 1, "word", some "Pieter"⟩, ⟨4, 1, "word", some "Arabisch"⟩, ⟨5, 1, "word", some "willen"⟩, ⟨6, 1, "word", some "laten"⟩, ⟨7, 1, "word", some "zien"⟩, ⟨8, 1, "word", some "schrijven"⟩]
    paperFeatures := [] }

def ex31 : Datum :=
  { id := "pullumgazdar1982_ex31"
    source := ⟨"pullum-gazdar-1982", "(31)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(dat Jan) Marie Arabisch Pieter wil laten zien schrijven"
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Marie", "Marie"), ("Arabisch", "Arabic"), ("Pieter", "Pieter"), ("wil", "will"), ("laten", "let"), ("zien", "see"), ("schrijven", "write")]
    glossedWords := [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['J', 'a', 'n'], ['J', 'a', 'n'], [⟨['J', 'a', 'n'], ['J', 'a', 'n'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], [⟨['A', 'r', 'a', 'b', 'i', 's', 'c', 'h'], ['A', 'r', 'a', 'b', 'i', 'c'], none⟩]⟩, ⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], [⟨['P', 'i', 'e', 't', 'e', 'r'], ['P', 'i', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['w', 'i', 'l'], ['w', 'i', 'l', 'l'], [⟨['w', 'i', 'l'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['l', 'a', 't', 'e', 'n'], ['l', 'e', 't'], [⟨['l', 'a', 't', 'e', 'n'], ['l', 'e', 't'], none⟩]⟩, ⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], [⟨['z', 'i', 'e', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], [⟨['s', 'c', 'h', 'r', 'i', 'j', 'v', 'e', 'n'], ['w', 'r', 'i', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 7, "verb phrase", none⟩, ⟨2, 1, "word", some "Marie"⟩, ⟨3, 1, "word", some "Arabisch"⟩, ⟨4, 1, "word", some "Pieter"⟩, ⟨5, 1, "word", some "willen"⟩, ⟨6, 1, "word", some "laten"⟩, ⟨7, 1, "word", some "zien"⟩, ⟨8, 1, "word", some "schrijven"⟩]
    paperFeatures := [] }

def ex38 : Datum :=
  { id := "pullumgazdar1982_ex38"
    source := ⟨"pullum-gazdar-1982", "(38)"⟩
    reportedIn := none
    method := some .elicitation
    language := "moha1258"
    primaryText := "iʔi knuhsnuhweʔs thikʌ kanuhsa"
    glossedTokens := [("iʔi", "I"), ("knuhsnuhweʔs", "house-like"), ("thikʌ", "that"), ("kanuhsa", "house")]
    glossedWords := [⟨['i', 'ʔ', 'i'], ['I'], [⟨['i', 'ʔ', 'i'], ['I'], none⟩]⟩, ⟨['k', 'n', 'u', 'h', 's', 'n', 'u', 'h', 'w', 'e', 'ʔ', 's'], ['h', 'o', 'u', 's', 'e', '-', 'l', 'i', 'k', 'e'], []⟩, ⟨['t', 'h', 'i', 'k', 'ʌ'], ['t', 'h', 'a', 't'], [⟨['t', 'h', 'i', 'k', 'ʌ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'a', 'n', 'u', 'h', 's', 'a'], ['h', 'o', 'u', 's', 'e'], [⟨['k', 'a', 'n', 'u', 'h', 's', 'a'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "incorporated", some "nuhs"⟩, ⟨3, 1, "external", some "nuhs"⟩]
    paperFeatures := [] }

def ex39 : Datum :=
  { id := "pullumgazdar1982_ex39"
    source := ⟨"pullum-gazdar-1982", "(39)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "waʔkhnekahnínuʔ ne otsìʔtsaʔ"
    glossedTokens := [("waʔkhnekahnínuʔ", "I-liquid-bought"), ("ne", ""), ("otsìʔtsaʔ", "flower/wine")]
    glossedWords := [⟨['w', 'a', 'ʔ', 'k', 'h', 'n', 'e', 'k', 'a', 'h', 'n', 'í', 'n', 'u', 'ʔ'], ['I', '-', 'l', 'i', 'q', 'u', 'i', 'd', '-', 'b', 'o', 'u', 'g', 'h', 't'], []⟩, ⟨['n', 'e'], [], [⟨['n', 'e'], [], none⟩]⟩, ⟨['o', 't', 's', 'ì', 'ʔ', 't', 's', 'a', 'ʔ'], ['f', 'l', 'o', 'w', 'e', 'r', '/', 'w', 'i', 'n', 'e'], [⟨['o', 't', 's', 'ì', 'ʔ', 't', 's', 'a', 'ʔ'], ['f', 'l', 'o', 'w', 'e', 'r', '/', 'w', 'i', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "incorporated", some "hnek"⟩, ⟨2, 1, "external", some "tsiʔts"⟩]
    paperFeatures := [] }

def ex40 : Datum :=
  { id := "pullumgazdar1982_ex40"
    source := ⟨"pullum-gazdar-1982", "(40)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "wakeselehtahni:nuʔseʔ neʔ 'bike'"
    glossedTokens := [("wakeselehtahni:nuʔseʔ", "I her-vehicle-bought"), ("neʔ", ""), ("'bike'", "bike")]
    glossedWords := [⟨['w', 'a', 'k', 'e', 's', 'e', 'l', 'e', 'h', 't', 'a', 'h', 'n', 'i', ':', 'n', 'u', 'ʔ', 's', 'e', 'ʔ'], ['I', ' ', 'h', 'e', 'r', '-', 'v', 'e', 'h', 'i', 'c', 'l', 'e', '-', 'b', 'o', 'u', 'g', 'h', 't'], []⟩, ⟨['n', 'e', 'ʔ'], [], [⟨['n', 'e', 'ʔ'], [], none⟩]⟩, ⟨['\'', 'b', 'i', 'k', 'e', '\''], ['b', 'i', 'k', 'e'], [⟨['\'', 'b', 'i', 'k', 'e', '\''], ['b', 'i', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "incorporated", some "seleht"⟩, ⟨2, 1, "external", some "bike"⟩]
    paperFeatures := [] }

def ex41a : Datum :=
  { id := "pullumgazdar1982_ex41a"
    source := ⟨"pullum-gazdar-1982", "(41a)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "kanuhsrakʌ thikʌ kanuhsa"
    glossedTokens := [("kanuhsrakʌ", "it-house-white"), ("thikʌ", "that"), ("kanuhsa", "house")]
    glossedWords := [⟨['k', 'a', 'n', 'u', 'h', 's', 'r', 'a', 'k', 'ʌ'], ['i', 't', '-', 'h', 'o', 'u', 's', 'e', '-', 'w', 'h', 'i', 't', 'e'], []⟩, ⟨['t', 'h', 'i', 'k', 'ʌ'], ['t', 'h', 'a', 't'], [⟨['t', 'h', 'i', 'k', 'ʌ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'a', 'n', 'u', 'h', 's', 'a'], ['h', 'o', 'u', 's', 'e'], [⟨['k', 'a', 'n', 'u', 'h', 's', 'a'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "incorporated", some "nuhs"⟩, ⟨2, 1, "external", some "nuhs"⟩]
    paperFeatures := [] }

def ex41b : Datum :=
  { id := "pullumgazdar1982_ex41b"
    source := ⟨"pullum-gazdar-1982", "(41b)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "kanuhsrakʌ thikʌ"
    glossedTokens := [("kanuhsrakʌ", "it-house-white"), ("thikʌ", "that")]
    glossedWords := [⟨['k', 'a', 'n', 'u', 'h', 's', 'r', 'a', 'k', 'ʌ'], ['i', 't', '-', 'h', 'o', 'u', 's', 'e', '-', 'w', 'h', 'i', 't', 'e'], []⟩, ⟨['t', 'h', 'i', 'k', 'ʌ'], ['t', 'h', 'a', 't'], [⟨['t', 'h', 'i', 'k', 'ʌ'], ['t', 'h', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "incorporated", some "nuhs"⟩]
    paperFeatures := [] }

def ex42 : Datum :=
  { id := "pullumgazdar1982_ex42"
    source := ⟨"pullum-gazdar-1982", "(42)"⟩
    reportedIn := none
    method := some .corpus
    language := "moha1258"
    primaryText := "keliʔwanú:weʔs kiʔ"
    glossedTokens := [("keliʔwanú:weʔs", "I it-idea-like"), ("kiʔ", "this")]
    glossedWords := [⟨['k', 'e', 'l', 'i', 'ʔ', 'w', 'a', 'n', 'ú', ':', 'w', 'e', 'ʔ', 's'], ['I', ' ', 'i', 't', '-', 'i', 'd', 'e', 'a', '-', 'l', 'i', 'k', 'e'], []⟩, ⟨['k', 'i', 'ʔ'], ['t', 'h', 'i', 's'], [⟨['k', 'i', 'ʔ'], ['t', 'h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "incorporated", some "liʔw"⟩]
    paperFeatures := [] }

def ex43a : Datum :=
  { id := "pullumgazdar1982_ex43a"
    source := ⟨"pullum-gazdar-1982", "(43a)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi k-nuhweʔs ne ka-nuhs-aʔ"
    glossedTokens := [("iʔi", "I"), ("k-nuhweʔs", "like"), ("ne", ""), ("ka-nuhs-aʔ", "house")]
    glossedWords := [⟨['i', 'ʔ', 'i'], ['I'], [⟨['i', 'ʔ', 'i'], ['I'], none⟩]⟩, ⟨['k', '-', 'n', 'u', 'h', 'w', 'e', 'ʔ', 's'], ['l', 'i', 'k', 'e'], []⟩, ⟨['n', 'e'], [], [⟨['n', 'e'], [], none⟩]⟩, ⟨['k', 'a', '-', 'n', 'u', 'h', 's', '-', 'a', 'ʔ'], ['h', 'o', 'u', 's', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "external", some "nuhs"⟩]
    paperFeatures := [] }

def ex43b : Datum :=
  { id := "pullumgazdar1982_ex43b"
    source := ⟨"pullum-gazdar-1982", "(43b)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi k-nuhweʔs ne sawatis hra-o-nuhs-aʔ"
    glossedTokens := [("iʔi", "I"), ("k-nuhweʔs", "like"), ("ne", ""), ("sawatis", "John('s)"), ("hra-o-nuhs-aʔ", "house")]
    glossedWords := [⟨['i', 'ʔ', 'i'], ['I'], [⟨['i', 'ʔ', 'i'], ['I'], none⟩]⟩, ⟨['k', '-', 'n', 'u', 'h', 'w', 'e', 'ʔ', 's'], ['l', 'i', 'k', 'e'], []⟩, ⟨['n', 'e'], [], [⟨['n', 'e'], [], none⟩]⟩, ⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n', '(', '\'', 's', ')'], [⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n', '(', '\'', 's', ')'], none⟩]⟩, ⟨['h', 'r', 'a', '-', 'o', '-', 'n', 'u', 'h', 's', '-', 'a', 'ʔ'], ['h', 'o', 'u', 's', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "external", some "nuhs"⟩]
    paperFeatures := [] }

def ex43c : Datum :=
  { id := "pullumgazdar1982_ex43c"
    source := ⟨"pullum-gazdar-1982", "(43c)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi k-nuhs-nuhweʔs ne sawatis hrao-nuhs-aʔ"
    glossedTokens := [("iʔi", "I"), ("k-nuhs-nuhweʔs", "house-like"), ("ne", ""), ("sawatis", "John('s)"), ("hrao-nuhs-aʔ", "house")]
    glossedWords := [⟨['i', 'ʔ', 'i'], ['I'], [⟨['i', 'ʔ', 'i'], ['I'], none⟩]⟩, ⟨['k', '-', 'n', 'u', 'h', 's', '-', 'n', 'u', 'h', 'w', 'e', 'ʔ', 's'], ['h', 'o', 'u', 's', 'e', '-', 'l', 'i', 'k', 'e'], []⟩, ⟨['n', 'e'], [], [⟨['n', 'e'], [], none⟩]⟩, ⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n', '(', '\'', 's', ')'], [⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n', '(', '\'', 's', ')'], none⟩]⟩, ⟨['h', 'r', 'a', 'o', '-', 'n', 'u', 'h', 's', '-', 'a', 'ʔ'], ['h', 'o', 'u', 's', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "incorporated", some "nuhs"⟩, ⟨4, 1, "external", some "nuhs"⟩]
    paperFeatures := [] }

def ex43d : Datum :=
  { id := "pullumgazdar1982_ex43d"
    source := ⟨"pullum-gazdar-1982", "(43d)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi hrai-nuhs-nuhweʔs ne sawatis"
    glossedTokens := [("iʔi", "I"), ("hrai-nuhs-nuhweʔs", "house-like"), ("ne", ""), ("sawatis", "John")]
    glossedWords := [⟨['i', 'ʔ', 'i'], ['I'], [⟨['i', 'ʔ', 'i'], ['I'], none⟩]⟩, ⟨['h', 'r', 'a', 'i', '-', 'n', 'u', 'h', 's', '-', 'n', 'u', 'h', 'w', 'e', 'ʔ', 's'], ['h', 'o', 'u', 's', 'e', '-', 'l', 'i', 'k', 'e'], []⟩, ⟨['n', 'e'], [], [⟨['n', 'e'], [], none⟩]⟩, ⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n'], [⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "incorporated", some "nuhs"⟩, ⟨3, 1, "external", some "sawatis"⟩]
    paperFeatures := [] }

def ex43e : Datum :=
  { id := "pullumgazdar1982_ex43e"
    source := ⟨"pullum-gazdar-1982", "(43e)"⟩
    reportedIn := none
    language := "moha1258"
    primaryText := "iʔi hrai-nuhweʔs ne sawatis hrao-nuhs-aʔ"
    glossedTokens := [("iʔi", "I"), ("hrai-nuhweʔs", "like"), ("ne", ""), ("sawatis", "John('s)"), ("hrao-nuhs-aʔ", "house")]
    glossedWords := [⟨['i', 'ʔ', 'i'], ['I'], [⟨['i', 'ʔ', 'i'], ['I'], none⟩]⟩, ⟨['h', 'r', 'a', 'i', '-', 'n', 'u', 'h', 'w', 'e', 'ʔ', 's'], ['l', 'i', 'k', 'e'], []⟩, ⟨['n', 'e'], [], [⟨['n', 'e'], [], none⟩]⟩, ⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n', '(', '\'', 's', ')'], [⟨['s', 'a', 'w', 'a', 't', 'i', 's'], ['J', 'o', 'h', 'n', '(', '\'', 's', ')'], none⟩]⟩, ⟨['h', 'r', 'a', 'o', '-', 'n', 'u', 'h', 's', '-', 'a', 'ʔ'], ['h', 'o', 'u', 's', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "external", some "nuhs"⟩]
    paperFeatures := [] }

def all : List Datum := [ex18a, ex18b, ex18c, ex18d, ex19a, ex19b, ex25, ex26, ex27, ex28, ex31, ex38, ex39, ex40, ex41a, ex41b, ex42, ex43a, ex43b, ex43c, ex43d, ex43e]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- subject: the head noun of a conjoined subject of a *respectively* sentence, whose entry the lexeme names -/
  | subject
  /-- verb: a conjoined verb of a *respectively* sentence, whose entry the lexeme names -/
  | verb
  /-- verb phrase: the Dutch verb phrase that the grammar generates, bracketed in the paper's examples -/
  | verbPhrase
  /-- word: a word of the Dutch verb phrase, which the lexeme names -/
  | word
  /-- incorporated: a Mohawk verb with an incorporated noun stem, which the lexeme names -/
  | incorporated
  /-- external: the head noun of the external noun phrase of a Mohawk verb, whose stem the lexeme names -/
  | external
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("subject", .subject), ("verb", .verb), ("verb phrase", .verbPhrase), ("word", .word), ("incorporated", .incorporated), ("external", .external)]

/-- The entries of the English, Dutch and Mohawk words that the spans mark. -/
inductive Lexeme where
  /-- woman: the English noun -/
  | woman
  /-- man: the English noun -/
  | man
  /-- smoke: the English verb -/
  | smoke
  /-- drink: the English verb -/
  | drink
  /-- Marie: Dutch, a personal name -/
  | marie
  /-- Pieter: Dutch, a personal name -/
  | pieter
  /-- Arabisch: Dutch 'Arabic' -/
  | arabisch
  /-- Hans: Dutch, a personal name -/
  | hans
  /-- laten: Dutch 'let' -/
  | laten
  /-- zien: Dutch 'see' -/
  | zien
  /-- willen: Dutch 'want' -/
  | willen
  /-- schrijven: Dutch 'write' -/
  | schrijven
  /-- liegen: Dutch 'lie' -/
  | liegen
  /-- nuhs: Mohawk 'house' -/
  | nuhs
  /-- hnek: Mohawk 'liquid' -/
  | hnek
  /-- tsiʔts: Mohawk 'flower', 'wine' -/
  | tsits
  /-- seleht: Mohawk 'vehicle' -/
  | seleht
  /-- bike: the English loan 'bike' in Mohawk -/
  | bike
  /-- liʔw: Mohawk 'idea', 'matter' -/
  | liw
  /-- sawatis: Mohawk, the name 'John' -/
  | sawatis
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("woman", .woman), ("man", .man), ("smoke", .smoke), ("drink", .drink), ("Marie", .marie), ("Pieter", .pieter), ("Arabisch", .arabisch), ("Hans", .hans), ("laten", .laten), ("zien", .zien), ("willen", .willen), ("schrijven", .schrijven), ("liegen", .liegen), ("nuhs", .nuhs), ("hnek", .hnek), ("tsiʔts", .tsits), ("seleht", .seleht), ("bike", .bike), ("liʔw", .liw), ("sawatis", .sawatis)])

end PullumGazdar1982.Examples
