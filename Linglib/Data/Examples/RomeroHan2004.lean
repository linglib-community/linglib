module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `RomeroHan2004` — typed example data

Auto-generated from `Linglib/Data/Examples/RomeroHan2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RomeroHan2004.Examples`.
-/

@[expose] public section

namespace RomeroHan2004.Examples

def doesnt_john_drink : Datum :=
  { id := "romerohan2004_doesnt_john_drink"
    source := ⟨"romero-han-2004", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Doesn't John drink?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def does_john_not_drink : Datum :=
  { id := "romerohan2004_does_john_not_drink"
    source := ⟨"romero-han-2004", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John not drink?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def does_john_drink : Datum :=
  { id := "romerohan2004_does_john_drink"
    source := ⟨"romero-han-2004", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John drink?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "none"), ("bias", "none")] }

def does_john_really_drink : Datum :=
  { id := "romerohan2004_does_john_really_drink"
    source := ⟨"romero-han-2004", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does John really drink?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "none"), ("emphasis", "really"), ("bias", "negative")] }

def isnt_jane_coming : Datum :=
  { id := "romerohan2004_isnt_jane_coming"
    source := ⟨"romero-han-2004", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Isn't Jane coming?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def isnt_jane_coming_too : Datum :=
  { id := "romerohan2004_isnt_jane_coming_too"
    source := ⟨"romero-han-2004", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Isn't Jane coming too?"
    glossedTokens := [("Isn't", ""), ("Jane", ""), ("coming", ""), ("too?", "")]
    glossedWords := [⟨['I', 's', 'n', '\'', 't'], [], [⟨['I', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'o', 'o', '?'], [], [⟨['t', 'o', 'o'], [], none⟩]⟩]
    context := "A: Ok, now that Stephan has come, we are all here. Let's go!"
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "polarityItem", some "too"⟩]
    paperFeatures := [("negation", "preposed"), ("bias", "positive"), ("scenario", "contradictionP")] }

def isnt_jane_coming_either : Datum :=
  { id := "romerohan2004_isnt_jane_coming_either"
    source := ⟨"romero-han-2004", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Isn't Jane coming either?"
    glossedTokens := [("Isn't", ""), ("Jane", ""), ("coming", ""), ("either?", "")]
    glossedWords := [⟨['I', 's', 'n', '\'', 't'], [], [⟨['I', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r', '?'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩]
    context := "Pat and Jane are two phonologists who are supposed to be speaking in our workshop on optimality and acquisition. A: Pat is not coming. So we don't have any phonologists in the program."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "polarityItem", some "either"⟩]
    paperFeatures := [("negation", "preposed"), ("bias", "positive"), ("scenario", "contradictionP")] }

def is_jane_really_coming_too : Datum :=
  { id := "romerohan2004_is_jane_really_coming_too"
    source := ⟨"romero-han-2004", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jane really coming too?"
    glossedTokens := [("Is", ""), ("Jane", ""), ("really", ""), ("coming", ""), ("too?", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['r', 'e', 'a', 'l', 'l', 'y'], [], [⟨['r', 'e', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'o', 'o', '?'], [], [⟨['t', 'o', 'o'], [], none⟩]⟩]
    context := "A: Pat already came, but we still have to wait for Jane."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "polarityItem", some "too"⟩]
    paperFeatures := [("negation", "none"), ("emphasis", "really")] }

def is_jane_really_coming_either : Datum :=
  { id := "romerohan2004_is_jane_really_coming_either"
    source := ⟨"romero-han-2004", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jane really coming either?"
    glossedTokens := [("Is", ""), ("Jane", ""), ("really", ""), ("coming", ""), ("either?", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['r', 'e', 'a', 'l', 'l', 'y'], [], [⟨['r', 'e', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r', '?'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩]
    context := "A: Pat is not coming. And we don't need to wait for Jane either."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "polarityItem", some "either"⟩]
    paperFeatures := [("negation", "none"), ("emphasis", "really")] }

def is_jane_not_coming_too : Datum :=
  { id := "romerohan2004_is_jane_not_coming_too"
    source := ⟨"romero-han-2004", "(79)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jane NOT coming too?"
    glossedTokens := [("Is", ""), ("Jane", ""), ("NOT", ""), ("coming", ""), ("too?", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['N', 'O', 'T'], [], [⟨['N', 'O', 'T'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'o', 'o', '?'], [], [⟨['t', 'o', 'o'], [], none⟩]⟩]
    context := "A: Pat already came, but we still have to wait for Jane."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "polarityItem", some "too"⟩]
    paperFeatures := [("negation", "nonPreposed"), ("emphasis", "stressedNot")] }

def is_jane_not_coming_either : Datum :=
  { id := "romerohan2004_is_jane_not_coming_either"
    source := ⟨"romero-han-2004", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jane NOT coming either?"
    glossedTokens := [("Is", ""), ("Jane", ""), ("NOT", ""), ("coming", ""), ("either?", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['N', 'O', 'T'], [], [⟨['N', 'O', 'T'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r', '?'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩]
    context := "A: Pat is not coming. And we don't need to wait for Jane ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "polarityItem", some "either"⟩]
    paperFeatures := [("negation", "nonPreposed"), ("emphasis", "stressedNot")] }

def greek_preposed : Datum :=
  { id := "romerohan2004_greek_preposed"
    source := ⟨"romero-han-2004", "(14a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Den ipie o Yannis kafe?"
    glossedTokens := [("Den", "NEG"), ("ipie", "drank"), ("o", "the"), ("Yannis", "Yannis"), ("kafe?", "coffee")]
    glossedWords := [⟨['D', 'e', 'n'], ['N', 'E', 'G'], [⟨['D', 'e', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['i', 'p', 'i', 'e'], ['d', 'r', 'a', 'n', 'k'], [⟨['i', 'p', 'i', 'e'], ['d', 'r', 'a', 'n', 'k'], none⟩]⟩, ⟨['o'], ['t', 'h', 'e'], [⟨['o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Y', 'a', 'n', 'n', 'i', 's'], ['Y', 'a', 'n', 'n', 'i', 's'], [⟨['Y', 'a', 'n', 'n', 'i', 's'], ['Y', 'a', 'n', 'n', 'i', 's'], none⟩]⟩, ⟨['k', 'a', 'f', 'e', '?'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['k', 'a', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def greek_nonpreposed : Datum :=
  { id := "romerohan2004_greek_nonpreposed"
    source := ⟨"romero-han-2004", "(14b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Yannis den ipie kafe?"
    glossedTokens := [("O", "the"), ("Yannis", "Yannis"), ("den", "NEG"), ("ipie", "drank"), ("kafe?", "coffee")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Y', 'a', 'n', 'n', 'i', 's'], ['Y', 'a', 'n', 'n', 'i', 's'], [⟨['Y', 'a', 'n', 'n', 'i', 's'], ['Y', 'a', 'n', 'n', 'i', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['N', 'E', 'G'], [⟨['d', 'e', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['i', 'p', 'i', 'e'], ['d', 'r', 'a', 'n', 'k'], [⟨['i', 'p', 'i', 'e'], ['d', 'r', 'a', 'n', 'k'], none⟩]⟩, ⟨['k', 'a', 'f', 'e', '?'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['k', 'a', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def spanish_preposed : Datum :=
  { id := "romerohan2004_spanish_preposed"
    source := ⟨"romero-han-2004", "(15a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿No bebe Juan?"
    glossedTokens := [("¿No", "NEG"), ("bebe", "drink"), ("Juan?", "Juan")]
    glossedWords := [⟨['¿', 'N', 'o'], ['N', 'E', 'G'], [⟨['¿', 'N', 'o'], ['N', 'E', 'G'], none⟩]⟩, ⟨['b', 'e', 'b', 'e'], ['d', 'r', 'i', 'n', 'k'], [⟨['b', 'e', 'b', 'e'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩, ⟨['J', 'u', 'a', 'n', '?'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def spanish_nonpreposed : Datum :=
  { id := "romerohan2004_spanish_nonpreposed"
    source := ⟨"romero-han-2004", "(15b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Juan no bebe?"
    glossedTokens := [("¿Juan", "Juan"), ("no", "NEG"), ("bebe?", "drink")]
    glossedWords := [⟨['¿', 'J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['¿', 'J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['n', 'o'], ['N', 'E', 'G'], [⟨['n', 'o'], ['N', 'E', 'G'], none⟩]⟩, ⟨['b', 'e', 'b', 'e', '?'], ['d', 'r', 'i', 'n', 'k'], [⟨['b', 'e', 'b', 'e'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def bulgarian_preposed : Datum :=
  { id := "romerohan2004_bulgarian_preposed"
    source := ⟨"romero-han-2004", "(16a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Ne pie li Ivan kafe?"
    glossedTokens := [("Ne", "NEG"), ("pie", "drink"), ("li", "li"), ("Ivan", "Ivan"), ("kafe?", "coffee")]
    glossedWords := [⟨['N', 'e'], ['N', 'E', 'G'], [⟨['N', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['p', 'i', 'e'], ['d', 'r', 'i', 'n', 'k'], [⟨['p', 'i', 'e'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩, ⟨['l', 'i'], ['l', 'i'], [⟨['l', 'i'], ['l', 'i'], none⟩]⟩, ⟨['I', 'v', 'a', 'n'], ['I', 'v', 'a', 'n'], [⟨['I', 'v', 'a', 'n'], ['I', 'v', 'a', 'n'], none⟩]⟩, ⟨['k', 'a', 'f', 'e', '?'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['k', 'a', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def bulgarian_nonpreposed : Datum :=
  { id := "romerohan2004_bulgarian_nonpreposed"
    source := ⟨"romero-han-2004", "(16b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Dali Ivan ne pie kafe?"
    glossedTokens := [("Dali", "Dali"), ("Ivan", "Ivan"), ("ne", "NEG"), ("pie", "drink"), ("kafe?", "coffee")]
    glossedWords := [⟨['D', 'a', 'l', 'i'], ['D', 'a', 'l', 'i'], [⟨['D', 'a', 'l', 'i'], ['D', 'a', 'l', 'i'], none⟩]⟩, ⟨['I', 'v', 'a', 'n'], ['I', 'v', 'a', 'n'], [⟨['I', 'v', 'a', 'n'], ['I', 'v', 'a', 'n'], none⟩]⟩, ⟨['n', 'e'], ['N', 'E', 'G'], [⟨['n', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['p', 'i', 'e'], ['d', 'r', 'i', 'n', 'k'], [⟨['p', 'i', 'e'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩, ⟨['k', 'a', 'f', 'e', '?'], ['c', 'o', 'f', 'f', 'e', 'e'], [⟨['k', 'a', 'f', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def german_preposed : Datum :=
  { id := "romerohan2004_german_preposed"
    source := ⟨"romero-han-2004", "(17a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat (nicht) Hans (nicht) Maria gesehen?"
    glossedTokens := [("Hat", "has"), ("(nicht)", "NEG"), ("Hans", "Hans"), ("(nicht)", "NEG"), ("Maria", "Maria"), ("gesehen?", "seen")]
    glossedWords := [⟨['H', 'a', 't'], ['h', 'a', 's'], [⟨['H', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['(', 'n', 'i', 'c', 'h', 't', ')'], ['N', 'E', 'G'], [⟨['n', 'i', 'c', 'h', 't'], ['N', 'E', 'G'], none⟩]⟩, ⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['(', 'n', 'i', 'c', 'h', 't', ')'], ['N', 'E', 'G'], [⟨['n', 'i', 'c', 'h', 't'], ['N', 'E', 'G'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['g', 'e', 's', 'e', 'h', 'e', 'n', '?'], ['s', 'e', 'e', 'n'], [⟨['g', 'e', 's', 'e', 'h', 'e', 'n'], ['s', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def german_nonpreposed : Datum :=
  { id := "romerohan2004_german_nonpreposed"
    source := ⟨"romero-han-2004", "(17b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hat Hans Maria nicht gesehen?"
    glossedTokens := [("Hat", "has"), ("Hans", "Hans"), ("Maria", "Maria"), ("nicht", "NEG"), ("gesehen?", "seen")]
    glossedWords := [⟨['H', 'a', 't'], ['h', 'a', 's'], [⟨['H', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['N', 'E', 'G'], [⟨['n', 'i', 'c', 'h', 't'], ['N', 'E', 'G'], none⟩]⟩, ⟨['g', 'e', 's', 'e', 'h', 'e', 'n', '?'], ['s', 'e', 'e', 'n'], [⟨['g', 'e', 's', 'e', 'h', 'e', 'n'], ['s', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def korean_preposed : Datum :=
  { id := "romerohan2004_korean_preposed"
    source := ⟨"romero-han-2004", "(18a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Suni-ka coffee-lul masi-ess-ci anh-ni?"
    glossedTokens := [("Suni-ka", "Suni-NOM"), ("coffee-lul", "coffee-ACC"), ("masi-ess-ci", "drink-PST"), ("anh-ni?", "NEG-Q")]
    glossedWords := [⟨['S', 'u', 'n', 'i', '-', 'k', 'a'], ['S', 'u', 'n', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'u', 'n', 'i'], ['S', 'u', 'n', 'i'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['c', 'o', 'f', 'f', 'e', 'e', '-', 'l', 'u', 'l'], ['c', 'o', 'f', 'f', 'e', 'e', '-', 'A', 'C', 'C'], [⟨['c', 'o', 'f', 'f', 'e', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'a', 's', 'i', '-', 'e', 's', 's', '-', 'c', 'i'], ['d', 'r', 'i', 'n', 'k', '-', 'P', 'S', 'T'], []⟩, ⟨['a', 'n', 'h', '-', 'n', 'i', '?'], ['N', 'E', 'G', '-', 'Q'], [⟨['a', 'n', 'h'], ['N', 'E', 'G'], none⟩, ⟨['n', 'i'], ['Q'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "preposed"), ("bias", "positive")] }

def korean_nonpreposed_short : Datum :=
  { id := "romerohan2004_korean_nonpreposed_short"
    source := ⟨"romero-han-2004", "(18b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Suni-ka coffee-lul an masi-ess-ni?"
    glossedTokens := [("Suni-ka", "Suni-NOM"), ("coffee-lul", "coffee-ACC"), ("an", "NEG"), ("masi-ess-ni?", "drink-PST-Q")]
    glossedWords := [⟨['S', 'u', 'n', 'i', '-', 'k', 'a'], ['S', 'u', 'n', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'u', 'n', 'i'], ['S', 'u', 'n', 'i'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['c', 'o', 'f', 'f', 'e', 'e', '-', 'l', 'u', 'l'], ['c', 'o', 'f', 'f', 'e', 'e', '-', 'A', 'C', 'C'], [⟨['c', 'o', 'f', 'f', 'e', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a', 'n'], ['N', 'E', 'G'], [⟨['a', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['m', 'a', 's', 'i', '-', 'e', 's', 's', '-', 'n', 'i', '?'], ['d', 'r', 'i', 'n', 'k', '-', 'P', 'S', 'T', '-', 'Q'], [⟨['m', 'a', 's', 'i'], ['d', 'r', 'i', 'n', 'k'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['n', 'i'], ['Q'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def korean_nonpreposed_long : Datum :=
  { id := "romerohan2004_korean_nonpreposed_long"
    source := ⟨"romero-han-2004", "(18c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Suni-ka coffee-lul masi-ci anh-ess-ni?"
    glossedTokens := [("Suni-ka", "Suni-NOM"), ("coffee-lul", "coffee-ACC"), ("masi-ci", "drink"), ("anh-ess-ni?", "NEG-PST-Q")]
    glossedWords := [⟨['S', 'u', 'n', 'i', '-', 'k', 'a'], ['S', 'u', 'n', 'i', '-', 'N', 'O', 'M'], [⟨['S', 'u', 'n', 'i'], ['S', 'u', 'n', 'i'], none⟩, ⟨['k', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['c', 'o', 'f', 'f', 'e', 'e', '-', 'l', 'u', 'l'], ['c', 'o', 'f', 'f', 'e', 'e', '-', 'A', 'C', 'C'], [⟨['c', 'o', 'f', 'f', 'e', 'e'], ['c', 'o', 'f', 'f', 'e', 'e'], none⟩, ⟨['l', 'u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'a', 's', 'i', '-', 'c', 'i'], ['d', 'r', 'i', 'n', 'k'], []⟩, ⟨['a', 'n', 'h', '-', 'e', 's', 's', '-', 'n', 'i', '?'], ['N', 'E', 'G', '-', 'P', 'S', 'T', '-', 'Q'], [⟨['a', 'n', 'h'], ['N', 'E', 'G'], none⟩, ⟨['e', 's', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['n', 'i'], ['Q'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "nonPreposed"), ("bias", "none")] }

def isnt_jane_coming_either_95 : Datum :=
  { id := "romerohan2004_isnt_jane_coming_either_95"
    source := ⟨"romero-han-2004", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Isn't Jane coming either?"
    glossedTokens := [("Isn't", ""), ("Jane", ""), ("coming", ""), ("either?", "")]
    glossedWords := [⟨['I', 's', 'n', '\'', 't'], [], [⟨['I', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['e', 'i', 't', 'h', 'e', 'r', '?'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩]
    context := "Pat and Jane are two phonologists who are supposed to be speaking in our workshop on optimality and acquisition. S originally believes that Jane is not coming. A: Pat is not coming. But fortunately for the phonologists we still have Jane..."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "polarityItem", some "either"⟩]
    paperFeatures := [("negation", "preposed"), ("scenario", "contradictionNotP")] }

def isnt_jane_coming_too_100 : Datum :=
  { id := "romerohan2004_isnt_jane_coming_too_100"
    source := ⟨"romero-han-2004", "(100)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Isn't Jane coming too?"
    glossedTokens := [("Isn't", ""), ("Jane", ""), ("coming", ""), ("too?", "")]
    glossedWords := [⟨['I', 's', 'n', '\'', 't'], [], [⟨['I', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['t', 'o', 'o', '?'], [], [⟨['t', 'o', 'o'], [], none⟩]⟩]
    context := "S originally believes that Jane is not coming. A: Pat already came, but we still have to wait for Jane."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "polarityItem", some "too"⟩]
    paperFeatures := [("negation", "preposed"), ("scenario", "contradictionNotP")] }

def hasnt_frege_already_reviewed : Datum :=
  { id := "romerohan2004_hasnt_frege_already_reviewed"
    source := ⟨"romero-han-2004", "(105)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hasn't Frege already reviewed for us? He'd be a good one."
    glossedTokens := [("Hasn't", ""), ("Frege", ""), ("already", ""), ("reviewed", ""), ("for", ""), ("us?", ""), ("He'd", ""), ("be", ""), ("a", ""), ("good", ""), ("one.", "")]
    glossedWords := [⟨['H', 'a', 's', 'n', '\'', 't'], [], [⟨['H', 'a', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['F', 'r', 'e', 'g', 'e'], [], [⟨['F', 'r', 'e', 'g', 'e'], [], none⟩]⟩, ⟨['a', 'l', 'r', 'e', 'a', 'd', 'y'], [], [⟨['a', 'l', 'r', 'e', 'a', 'd', 'y'], [], none⟩]⟩, ⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], [⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['f', 'o', 'r'], [], [⟨['f', 'o', 'r'], [], none⟩]⟩, ⟨['u', 's', '?'], [], [⟨['u', 's'], [], none⟩]⟩, ⟨['H', 'e', '\'', 'd'], [], [⟨['H', 'e', '\'', 'd'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['g', 'o', 'o', 'd'], [], [⟨['g', 'o', 'o', 'd'], [], none⟩]⟩, ⟨['o', 'n', 'e', '.'], [], [⟨['o', 'n', 'e'], [], none⟩]⟩]
    context := "Dialog between two editors of a journal in 1900. A: I'd like to send this paper out to a senior reviewer, but I'd prefer somebody who has experience with our regulations."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "polarityItem", some "already"⟩]
    paperFeatures := [("negation", "preposed"), ("scenario", "suggestionP")] }

def hasnt_frege_reviewed_yet : Datum :=
  { id := "romerohan2004_hasnt_frege_reviewed_yet"
    source := ⟨"romero-han-2004", "(106)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hasn't Frege reviewed for us yet? He'd be a good one."
    glossedTokens := [("Hasn't", ""), ("Frege", ""), ("reviewed", ""), ("for", ""), ("us", ""), ("yet?", ""), ("He'd", ""), ("be", ""), ("a", ""), ("good", ""), ("one.", "")]
    glossedWords := [⟨['H', 'a', 's', 'n', '\'', 't'], [], [⟨['H', 'a', 's', 'n', '\'', 't'], [], none⟩]⟩, ⟨['F', 'r', 'e', 'g', 'e'], [], [⟨['F', 'r', 'e', 'g', 'e'], [], none⟩]⟩, ⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], [⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['f', 'o', 'r'], [], [⟨['f', 'o', 'r'], [], none⟩]⟩, ⟨['u', 's'], [], [⟨['u', 's'], [], none⟩]⟩, ⟨['y', 'e', 't', '?'], [], [⟨['y', 'e', 't'], [], none⟩]⟩, ⟨['H', 'e', '\'', 'd'], [], [⟨['H', 'e', '\'', 'd'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['g', 'o', 'o', 'd'], [], [⟨['g', 'o', 'o', 'd'], [], none⟩]⟩, ⟨['o', 'n', 'e', '.'], [], [⟨['o', 'n', 'e'], [], none⟩]⟩]
    context := "Dialog between two editors of a journal in 1900. A: I'd like to send this paper out to a senior reviewer, but I'd prefer somebody new."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "polarityItem", some "yet"⟩]
    paperFeatures := [("negation", "preposed"), ("scenario", "suggestionNotP")] }

def is_jane_really_coming : Datum :=
  { id := "romerohan2004_is_jane_really_coming"
    source := ⟨"romero-han-2004", "(110)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jane really coming?"
    glossedTokens := []
    context := "A: Pat already came, but we still have to wait for Jane."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "none"), ("emphasis", "really"), ("bias", "negative"), ("scenario", "contradictionNotP")] }

def has_frege_really_reviewed : Datum :=
  { id := "romerohan2004_has_frege_really_reviewed"
    source := ⟨"romero-han-2004", "(116)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has Frege really reviewed for us already? He'd be a good one."
    glossedTokens := [("Has", ""), ("Frege", ""), ("really", ""), ("reviewed", ""), ("for", ""), ("us", ""), ("already?", ""), ("He'd", ""), ("be", ""), ("a", ""), ("good", ""), ("one.", "")]
    glossedWords := [⟨['H', 'a', 's'], [], [⟨['H', 'a', 's'], [], none⟩]⟩, ⟨['F', 'r', 'e', 'g', 'e'], [], [⟨['F', 'r', 'e', 'g', 'e'], [], none⟩]⟩, ⟨['r', 'e', 'a', 'l', 'l', 'y'], [], [⟨['r', 'e', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], [⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['f', 'o', 'r'], [], [⟨['f', 'o', 'r'], [], none⟩]⟩, ⟨['u', 's'], [], [⟨['u', 's'], [], none⟩]⟩, ⟨['a', 'l', 'r', 'e', 'a', 'd', 'y', '?'], [], [⟨['a', 'l', 'r', 'e', 'a', 'd', 'y'], [], none⟩]⟩, ⟨['H', 'e', '\'', 'd'], [], [⟨['H', 'e', '\'', 'd'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['g', 'o', 'o', 'd'], [], [⟨['g', 'o', 'o', 'd'], [], none⟩]⟩, ⟨['o', 'n', 'e', '.'], [], [⟨['o', 'n', 'e'], [], none⟩]⟩]
    context := "Dialog between two editors of a journal in 1900. A: I'd like to send this paper out to a senior reviewer, and I'd prefer somebody who has experience with our regulations."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "polarityItem", some "already"⟩]
    paperFeatures := [("negation", "none"), ("emphasis", "really"), ("scenario", "suggestionP")] }

def is_jane_not_coming_117 : Datum :=
  { id := "romerohan2004_is_jane_not_coming_117"
    source := ⟨"romero-han-2004", "(117)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jane NOT coming (either)?"
    glossedTokens := [("Is", ""), ("Jane", ""), ("NOT", ""), ("coming", ""), ("(either)?", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['J', 'a', 'n', 'e'], [], [⟨['J', 'a', 'n', 'e'], [], none⟩]⟩, ⟨['N', 'O', 'T'], [], [⟨['N', 'O', 'T'], [], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'g'], [], [⟨['c', 'o', 'm', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['(', 'e', 'i', 't', 'h', 'e', 'r', ')', '?'], [], [⟨['e', 'i', 't', 'h', 'e', 'r'], [], none⟩]⟩]
    context := "A: Pat is not coming. And we don't need to wait for Jane..."
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "polarityItem", some "either"⟩]
    paperFeatures := [("negation", "nonPreposed"), ("emphasis", "stressedNot"), ("bias", "positive"), ("scenario", "contradictionP")] }

def has_frege_not_reviewed_yet : Datum :=
  { id := "romerohan2004_has_frege_not_reviewed_yet"
    source := ⟨"romero-han-2004", "(120)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has Frege NOT reviewed for us yet? He'd be a good one."
    glossedTokens := [("Has", ""), ("Frege", ""), ("NOT", ""), ("reviewed", ""), ("for", ""), ("us", ""), ("yet?", ""), ("He'd", ""), ("be", ""), ("a", ""), ("good", ""), ("one.", "")]
    glossedWords := [⟨['H', 'a', 's'], [], [⟨['H', 'a', 's'], [], none⟩]⟩, ⟨['F', 'r', 'e', 'g', 'e'], [], [⟨['F', 'r', 'e', 'g', 'e'], [], none⟩]⟩, ⟨['N', 'O', 'T'], [], [⟨['N', 'O', 'T'], [], none⟩]⟩, ⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], [⟨['r', 'e', 'v', 'i', 'e', 'w', 'e', 'd'], [], none⟩]⟩, ⟨['f', 'o', 'r'], [], [⟨['f', 'o', 'r'], [], none⟩]⟩, ⟨['u', 's'], [], [⟨['u', 's'], [], none⟩]⟩, ⟨['y', 'e', 't', '?'], [], [⟨['y', 'e', 't'], [], none⟩]⟩, ⟨['H', 'e', '\'', 'd'], [], [⟨['H', 'e', '\'', 'd'], [], none⟩]⟩, ⟨['b', 'e'], [], [⟨['b', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['g', 'o', 'o', 'd'], [], [⟨['g', 'o', 'o', 'd'], [], none⟩]⟩, ⟨['o', 'n', 'e', '.'], [], [⟨['o', 'n', 'e'], [], none⟩]⟩]
    context := "Dialog between two editors of a journal in 1900. A: I'd like to send this paper out to a senior reviewer, but I'd prefer somebody new who has not yet reviewed for us."
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "polarityItem", some "yet"⟩]
    paperFeatures := [("negation", "nonPreposed"), ("emphasis", "stressedNot"), ("scenario", "suggestionNotP")] }

def all : List Datum := [doesnt_john_drink, does_john_not_drink, does_john_drink, does_john_really_drink, isnt_jane_coming, isnt_jane_coming_too, isnt_jane_coming_either, is_jane_really_coming_too, is_jane_really_coming_either, is_jane_not_coming_too, is_jane_not_coming_either, greek_preposed, greek_nonpreposed, spanish_preposed, spanish_nonpreposed, bulgarian_preposed, bulgarian_nonpreposed, german_preposed, german_nonpreposed, korean_preposed, korean_nonpreposed_short, korean_nonpreposed_long, isnt_jane_coming_either_95, isnt_jane_coming_too_100, hasnt_frege_already_reviewed, hasnt_frege_reviewed_yet, is_jane_really_coming, has_frege_really_reviewed, is_jane_not_coming_117, has_frege_not_reviewed_yet]

/-- Where the negation of a yes/no question sits. -/
inductive NegationPlacement where
  /-- preposed: negation preposed with the finite verb -/
  | preposed
  /-- nonPreposed: negation in its clause-internal position -/
  | nonPreposed
  /-- none: a positive question -/
  | absent
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `negation`. -/
def negation (e : Datum) : Option NegationPlacement :=
  e.parse? "negation" [("preposed", .preposed), ("nonPreposed", .nonPreposed), ("none", .absent)]

/-- The epistemic implicature the paper reports for a question. -/
inductive Bias where
  /-- positive: the speaker believed or expected the proposition -/
  | positive
  /-- negative: the speaker believed or expected its negation -/
  | negative
  /-- none: no epistemic implicature is necessary -/
  | absent
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `bias`. -/
def bias (e : Datum) : Option Bias :=
  e.parse? "bias" [("positive", .positive), ("negative", .negative), ("none", .absent)]

/-- The emphasis on the polarity of a question. -/
inductive Emphasis where
  /-- really: the adverb really -/
  | really
  /-- stressedNot: focal stress on NOT -/
  | stressedNot
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `emphasis`. -/
def emphasis (e : Datum) : Option Emphasis :=
  e.parse? "emphasis" [("really", .really), ("stressedNot", .stressedNot)]

/-- The context a question is asked in, relative to its proposition p. -/
inductive Scenario where
  /-- contradictionP: the speaker believed p and the addressee implied ¬p -/
  | contradictionP
  /-- contradictionNotP: the speaker believed ¬p and the addressee implied p -/
  | contradictionNotP
  /-- suggestionP: the addressee raised a question he cannot answer, to which p is a possible answer -/
  | suggestionP
  /-- suggestionNotP: the addressee raised a question he cannot answer, to which ¬p is a possible answer -/
  | suggestionNotP
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `scenario`. -/
def scenario (e : Datum) : Option Scenario :=
  e.parse? "scenario" [("contradictionP", .contradictionP), ("contradictionNotP", .contradictionNotP),
    ("suggestionP", .suggestionP), ("suggestionNotP", .suggestionNotP)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- polarityItem: a polarity item of the question -/
  | polarityItem
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("polarityItem", .polarityItem)]

/-- The polarity items of the questions. -/
inductive Lexeme where
  /-- too: English too, additive -/
  | too
  /-- either: English either, additive -/
  | either
  /-- already: English already -/
  | already
  /-- yet: English yet -/
  | yet
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("too", .too), ("either", .either), ("already", .already), ("yet", .yet)])

end RomeroHan2004.Examples
